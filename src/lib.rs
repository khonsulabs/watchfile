//! An easy-to-use automatic file reloader.
#![forbid(unsafe_code)]
#![warn(missing_docs, clippy::pedantic)]
#![allow(clippy::module_name_repetitions)]
use std::borrow::Cow;
use std::collections::HashMap;
use std::convert::Infallible;
use std::ffi::OsStr;
use std::fmt::Debug;
use std::io::Read;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::path::Path;
use std::sync::{Arc, Mutex, MutexGuard, OnceLock, PoisonError};
use std::{env, fs, io};

use notify::{INotifyWatcher, Watcher};
use watchable::Watchable;

static FILE_WATCHERS: OnceLock<Mutex<GlobalWatchers>> = OnceLock::new();

#[derive(Default)]
struct GlobalWatchers {
    watcher_id: u64,
    watchers: HashMap<Arc<Path>, FolderWatchers>,
    scratch: Vec<u8>,
}

impl GlobalWatchers {
    pub fn watch(&mut self, path: &FilePath, reloader: Reloader) {
        let folder = self.watchers.entry(path.parent.clone()).or_default();
        let files = folder.files.entry(path.name.clone()).or_default();
        files.push(reloader);
    }

    pub fn unwatch(&mut self, token: &LoaderToken) {
        let folder = self
            .watchers
            .get_mut(&token.path.parent)
            .expect("missing parent");
        let loaders = folder
            .files
            .get_mut(&token.path.name)
            .expect("missing file");
        let index = loaders
            .iter_mut()
            .enumerate()
            .find_map(|(index, reloader)| (reloader.token == token.id).then_some(index))
            .expect("missing reloader");
        loaders.remove(index);
        if loaders.is_empty() {
            folder.files.remove(&token.path.name);
            if folder.files.is_empty() {
                self.watchers.remove(&token.path.parent);
            }
        }
    }
}

#[derive(Clone)]
struct FilePath {
    parent: Arc<Path>,
    name: Arc<OsStr>,
}

impl<'a> TryFrom<&'a Path> for FilePath {
    type Error = Error;

    fn try_from(path: &'_ Path) -> Result<Self, Self::Error> {
        let path = if path.is_absolute() {
            Cow::Borrowed(path)
        } else {
            Cow::Owned(env::current_dir()?.join(path))
        };
        match (path.parent(), path.file_name()) {
            (Some(parent), Some(name)) => Ok(Self {
                parent: Arc::from(parent),
                name: Arc::from(name),
            }),
            _ => Err(Error::InvalidPath),
        }
    }
}

#[derive(Default)]
struct FolderWatchers {
    files: HashMap<Arc<OsStr>, Vec<Reloader>>,
}

struct Reloader {
    reloader: Box<dyn AnyFileReloader>,
    token: u64,
}

impl Reloader {
    pub fn new(reloader: Box<dyn AnyFileReloader>, global: &mut GlobalWatchers) -> Self {
        let reloader = Self {
            reloader,
            token: global.watcher_id,
        };
        global.watcher_id += 1;
        reloader
    }

    pub fn new_token(&self, path: &FilePath) -> Arc<LoaderToken> {
        Arc::new(LoaderToken {
            id: self.token,
            path: path.clone(),
        })
    }
}

fn global_state() -> MutexGuard<'static, GlobalWatchers> {
    FILE_WATCHERS
        .get_or_init(Mutex::default)
        .lock()
        .map_or_else(PoisonError::into_inner, |g| g)
}

fn global_notify() -> Result<MutexGuard<'static, INotifyWatcher>, Arc<notify::Error>> {
    static WATCHER: OnceLock<Result<Mutex<INotifyWatcher>, Arc<notify::Error>>> = OnceLock::new();
    match WATCHER.get_or_init(|| {
        notify::recommended_watcher(file_notified)
            .map(Mutex::new)
            .map_err(Arc::new)
    }) {
        Ok(notify) => Ok(notify.lock().map_or_else(PoisonError::into_inner, |g| g)),
        Err(err) => Err(err.clone()),
    }
}

fn file_notified(result: notify::Result<notify::Event>) {
    let Ok(notify::Event{ kind: notify::EventKind::Create(_) | notify::EventKind::Modify(_), paths, .. }) = result else { return };

    let global = &mut *global_state();
    for path in paths {
        let (Some(parent), Some(name)) = (path.parent(), path.file_name()) else { continue };
        let Some(parent_watchers) = global.watchers.get_mut(parent) else { continue };
        let Some(watchers) = parent_watchers.files.get_mut(name) else { continue };
        for watcher in watchers {
            watcher.reloader.reload(&path, &mut global.scratch);
        }
        global.scratch.clear();
    }
}

struct FileReloader<Loader>
where
    Loader: WatchFileLoader,
{
    loader: Loader,
    contents: watchable::Watchable<FileState<Loader>>,
}

trait AnyFileReloader: Send + Sync {
    fn reload(&mut self, path: &Path, scratch: &mut Vec<u8>);
}

impl<Loader> AnyFileReloader for FileReloader<Loader>
where
    Loader: WatchFileLoader,
{
    fn reload(&mut self, path: &Path, scratch: &mut Vec<u8>) {
        match load_file(&mut self.loader, path, scratch) {
            Ok(new_contents) => {
                let mut guard = self.contents.write();
                guard.contents = Some(new_contents);
                guard.error = None;
            }
            Err(err) => {
                let mut guard = self.contents.write();
                guard.error = Some(err);
            }
        }
    }
}

/// A file that is being watched for changes.
pub struct WatchFile<Loader = FileContents>
where
    Loader: WatchFileLoader,
{
    loader_token: Arc<LoaderToken>,
    path: FilePath,
    contents: watchable::Watcher<FileState<Loader>>,
    _loader: PhantomData<Loader>,
}

impl<T> WatchFile<T>
where
    T: WatchFileLoader,
{
    /// Tries to observe changes at `path`, ignoring any errors that occur while
    /// trying to watch the file. The file will always be loaded at least once
    /// time, but if any errors occurred while trying to watch the file, the
    /// contents will never be reloaded.
    ///
    /// # Panics
    ///
    /// This function panics if `path` is not an absolute path or
    /// [`std::env::current_dir()`] returns an error.
    pub fn try_new(path: &Path, mut loader: T) -> Self {
        let mut global = global_state();
        let initial = load_file(&mut loader, path, &mut global.scratch);
        let path = FilePath::try_from(path).expect("invalid watch path");

        let loader = FileReloader {
            loader,
            contents: Watchable::new(FileState::new(initial)),
        };
        let contents = loader.contents.watch();
        let loader = Reloader::new(Box::new(loader), &mut global);
        let loader_token = loader.new_token(&path);
        global.watch(&path, loader);
        drop(global);

        if let Ok(mut global_notify) = global_notify() {
            let _result = global_notify.watch(&path.parent, notify::RecursiveMode::NonRecursive);
        }

        Self {
            loader_token,
            path,
            contents,
            _loader: PhantomData,
        }
    }

    /// Creates a new file watcher for `path`. The path provided should be a
    /// path to a file, not a directory.
    ///
    /// `loader` will be invoked once upon initialization and once for each time
    /// the file is observed to have changed.
    ///
    /// # Errors
    ///
    /// - `path` must be an absolute path or [`std::env::current_dir()`] must
    ///   return Ok, otherwise an error will be returned.
    /// - If an error occurs while configuring the file notifications, the error
    ///   will be returned.
    pub fn new(path: &Path, mut loader: T) -> Result<Self, Error<T::Error>> {
        let mut global = global_state();
        let initial = load_file(&mut loader, path, &mut global.scratch);
        let path = FilePath::try_from(path).map_err(Error::into_fallible)?;

        let loader = FileReloader {
            loader,
            contents: Watchable::new(FileState::new(initial)),
        };
        let contents = loader.contents.watch();
        let loader = Reloader::new(Box::new(loader), &mut global);
        let loader_token = loader.new_token(&path);
        global.watch(&path, loader);
        drop(global);

        global_notify()?.watch(&path.parent, notify::RecursiveMode::NonRecursive)?;
        Ok(Self {
            loader_token,
            path,
            contents,
            _loader: PhantomData,
        })
    }

    /// Checks if the current file status is valid.
    ///
    /// # Errors
    ///
    /// Returns an error if the latest update to the file resulted in an error.
    pub fn check(&self) -> Result<(), Error<T::Error>> {
        self.contents.peek().check()
    }

    /// Returns the most recent contents of the file, if available. This
    /// internally updates the read status for any watch operations provided by
    /// [`Watchable`].
    ///
    /// # Errors
    ///
    /// Returns an error if the file contents were never able to be read
    /// successfully.
    pub fn read_contents(&mut self) -> Result<WatchedContents<'_, T>, Error<T::Error>> {
        let guard = self.contents.read();
        if guard.contents.is_some() {
            Ok(WatchedContents(guard))
        } else {
            Err(guard
                .error
                .clone()
                .expect("error should be present if no contents"))
        }
    }

    /// Returns the most recent contents of the file, if available.
    ///
    /// # Errors
    ///
    /// Returns an error if the file contents were never able to be read
    /// successfully.
    pub fn contents(&self) -> Result<WatchedContents<'_, T>, Error<T::Error>> {
        let guard = self.contents.peek();
        if guard.contents.is_some() {
            Ok(WatchedContents(guard))
        } else {
            Err(guard
                .error
                .clone()
                .expect("error should be present if no contents"))
        }
    }
}

impl WatchFile<FileContents> {
    /// Creates a new file watcher for `path`. The path provided should be a
    /// path to a file, not a directory.
    ///
    /// The contents of the returned watcher is a `Vec<u8>`.
    ///
    /// # Errors
    ///
    /// - `path` must be an absolute path or [`std::env::current_dir()`] must
    ///   return Ok, otherwise an error will be returned.
    /// - If an error occurs while configuring the file notifications, the error
    ///   will be returned.
    pub fn watch(path: &Path) -> Result<Self, crate::Error> {
        Self::new(path, FileContents)
    }
}

impl<Contents, Error> WatchFile<MapLoader<Contents, Error>>
where
    Contents: Send + Sync + 'static,
    Error: Debug + Send + Sync + 'static,
{
    /// Creates a new file watcher for `path`. The path provided should be a
    /// path to a file, not a directory.
    ///
    /// `map` will be invoked once upon initialization and once for each time
    /// the file is observed to have changed.
    ///
    /// # Errors
    ///
    /// - `path` must be an absolute path or [`std::env::current_dir()`] must
    ///   return Ok, otherwise an error will be returned.
    /// - If an error occurs while configuring the file notifications, the error
    ///   will be returned.
    pub fn new_mapped(
        path: &Path,
        map: impl FnMut(&[u8]) -> Result<Contents, Error> + Send + Sync + 'static,
    ) -> Result<Self, crate::Error<Error>> {
        Self::new(
            path,
            MapLoader {
                map: LoaderFunction::Boxed(Box::new(map)),
                _types: PhantomData,
            },
        )
    }
}

impl<L> Clone for WatchFile<L>
where
    L: WatchFileLoader,
    L::Contents: Clone, // TODO These shouldn't be required, update watchable
{
    fn clone(&self) -> Self {
        Self {
            loader_token: self.loader_token.clone(),
            path: self.path.clone(),
            contents: self.contents.clone(),
            _loader: PhantomData,
        }
    }
}

/// The in-memory state of a [`WatchFile`].
///
/// This structure is similar to `Result` except that it always keeps the most
/// recent successful loading of the file. This ensures that observers can
/// retrieve valid data even if a parsing error occurs in a later reload. See [`FileState::check()`]
pub struct FileState<L>
where
    L: WatchFileLoader,
{
    contents: Option<L::Contents>,
    error: Option<Error<L::Error>>,
}

impl<L> FileState<L>
where
    L: WatchFileLoader,
{
    fn new(initial: Result<L::Contents, Error<L::Error>>) -> Self {
        match initial {
            Ok(contents) => Self {
                contents: Some(contents),
                error: None,
            },
            Err(err) => Self {
                contents: None,
                error: Some(err),
            },
        }
    }

    /// Checks if the current file status is valid.
    ///
    /// # Errors
    ///
    /// Returns an error if the latest update to the file resulted in an error.
    pub fn check(&self) -> Result<(), Error<L::Error>> {
        if let Some(err) = self.error.clone() {
            Err(err)
        } else {
            Ok(())
        }
    }
}

impl<L> Clone for FileState<L>
where
    L: WatchFileLoader,
    L::Contents: Clone,
{
    fn clone(&self) -> Self {
        Self {
            contents: self.contents.clone(),
            error: self.error.clone(),
        }
    }
}

/// A read guard accessing the concents of a [`WatchFile`].
pub struct WatchedContents<'a, L>(watchable::WatchableReadGuard<'a, FileState<L>>)
where
    L: WatchFileLoader;

impl<'a, L> Deref for WatchedContents<'a, L>
where
    L: WatchFileLoader,
{
    type Target = L::Contents;

    fn deref(&self) -> &Self::Target {
        self.0
            .contents
            .as_ref()
            .expect("checked before constructing")
    }
}

impl<Loader> Deref for WatchFile<Loader>
where
    Loader: WatchFileLoader,
{
    type Target = watchable::Watcher<FileState<Loader>>;

    fn deref(&self) -> &Self::Target {
        &self.contents
    }
}

impl<Loader> DerefMut for WatchFile<Loader>
where
    Loader: WatchFileLoader,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.contents
    }
}

impl<Loader> Drop for WatchFile<Loader>
where
    Loader: WatchFileLoader,
{
    fn drop(&mut self) {
        // When this is the last instance, the global watchers hashmap and this
        // have the only two references to the name.
        if Arc::strong_count(&self.loader_token) == 1 {}
    }
}

struct LoaderToken {
    id: u64,
    path: FilePath,
}

impl Drop for LoaderToken {
    fn drop(&mut self) {
        let mut global = global_state();
        global.unwatch(self);
    }
}

/// An error watching a file's contents.
#[derive(Debug)]
pub enum Error<LoaderError = Infallible> {
    /// An invalid path was provided.
    InvalidPath,
    /// An error occurred while loading the file.
    Loader(Arc<LoaderError>),
    /// An error occurred while trying to watch the file.
    Notify(Arc<notify::Error>),
    /// An error occurred while reading the file's contents.
    Io(Arc<io::Error>),
}

impl Error<Infallible> {
    #[must_use]
    fn into_fallible<E>(self) -> Error<E> {
        match self {
            Error::InvalidPath => Error::InvalidPath,
            Error::Notify(notify) => Error::Notify(notify),
            Error::Io(io) => Error::Io(io),
            Error::Loader(_) => unreachable!(),
        }
    }
}

impl<T> Clone for Error<T> {
    fn clone(&self) -> Self {
        match self {
            Self::InvalidPath => Self::InvalidPath,
            Self::Loader(arg0) => Self::Loader(arg0.clone()),
            Self::Notify(arg0) => Self::Notify(arg0.clone()),
            Self::Io(arg0) => Self::Io(arg0.clone()),
        }
    }
}

impl<T> From<Arc<notify::Error>> for Error<T> {
    fn from(value: Arc<notify::Error>) -> Self {
        Self::Notify(value)
    }
}

impl<T> From<notify::Error> for Error<T> {
    fn from(value: notify::Error) -> Self {
        Self::Notify(Arc::new(value))
    }
}

impl<T> From<io::Error> for Error<T> {
    fn from(value: io::Error) -> Self {
        Self::Io(Arc::new(value))
    }
}

/// A loader for a [`WatchFile`].
///
/// Loaders are responsible for transforming `&[u8]` into another type, or
/// returning an error if the contents are invalid.
pub trait WatchFileLoader: Send + Sync + 'static {
    /// The type the file contains.
    type Contents: Send + Sync + 'static;
    /// An error type that can occur while loading a file.
    type Error: Send + Sync + Debug + 'static;

    /// Loads `Self::Contents` from `data`.
    ///
    /// # Errors
    ///
    /// Returns an error if `data` could not be successfully converted to
    /// `Self::Contents`.
    fn load(&mut self, data: &[u8]) -> Result<Self::Contents, Self::Error>;
}
/// Loads a file
fn load_file<L>(
    loader: &mut L,
    path: &Path,
    scratch: &mut Vec<u8>,
) -> Result<L::Contents, Error<L::Error>>
where
    L: WatchFileLoader,
{
    scratch.clear();
    let mut file = fs::File::open(path)?;
    file.read_to_end(scratch)?;
    loader
        .load(scratch)
        .map_err(|err| Error::Loader(Arc::new(err)))
}

enum LoaderFunction<C, E> {
    Boxed(#[allow(clippy::type_complexity)] Box<dyn FnMut(&[u8]) -> Result<C, E> + Send + Sync>),
    Fn(fn(&[u8]) -> Result<C, E>),
}

struct MapLoader<C, E> {
    map: LoaderFunction<C, E>,
    _types: PhantomData<(C, E)>,
}

impl<C, E> WatchFileLoader for MapLoader<C, E>
where
    C: Send + Sync + 'static,
    E: Debug + Send + Sync + 'static,
{
    type Contents = C;

    type Error = E;

    fn load(&mut self, data: &[u8]) -> Result<Self::Contents, Self::Error> {
        match &mut self.map {
            LoaderFunction::Boxed(function) => function(data),
            LoaderFunction::Fn(function) => function(data),
        }
    }
}

/// A [`WatchFile`] that can be utilized in static variables.
pub struct StaticWatchFile<Loader = FileContents>
where
    Loader: WatchFileLoader,
{
    file: OnceLock<WatchFile<Loader>>,
    init: Mutex<Option<(&'static str, Loader)>>,
}

impl<Loader> StaticWatchFile<Loader>
where
    Loader: WatchFileLoader,
{
    /// Creates a new file watcher for `path`. The path provided should be a
    /// path to a file, not a directory.
    ///
    /// `loader` will be invoked once upon initialization and once for each time
    /// the file is observed to have changed.
    ///
    /// Internally, this type is lazy-initialized. The file will not be accessed
    /// until the first time this structure is accessed.
    ///
    /// # Errors
    ///
    /// - `path` must be an absolute path or [`std::env::current_dir()`] must
    ///   return Ok, otherwise an error will be returned.
    /// - If an error occurs while configuring the file notifications, the error
    ///   will be returned.
    #[must_use]
    pub const fn new(path: &'static str, loader: Loader) -> Self {
        Self {
            file: OnceLock::new(),
            init: Mutex::new(Some((path, loader))),
        }
    }
}

impl StaticWatchFile<FileContents> {
    /// Creates a new file watcher for `path`. The path provided should be a
    /// path to a file, not a directory.
    ///
    /// The contents of the returned watcher is a `Vec<u8>`.
    ///
    /// Internally, this type is lazy-initialized. The file will not be accessed
    /// until the first time this structure is accessed.
    #[must_use]
    pub const fn watch(path: &'static str) -> Self {
        Self::new(path, FileContents)
    }
}

impl<Contents, Error> StaticWatchFile<MapLoader<Contents, Error>>
where
    Contents: Send + Sync + 'static,
    Error: Debug + Send + Sync + 'static,
{
    /// Creates a new file watcher for `path`. The path provided should be a
    /// path to a file, not a directory.
    ///
    /// `map` will be invoked once upon initialization and once for each time
    /// the file is observed to have changed.
    ///
    /// Internally, this type is lazy-initialized. The file will not be accessed
    /// until the first time this structure is accessed.
    #[must_use]
    pub const fn new_mapped(path: &'static str, map: fn(&[u8]) -> Result<Contents, Error>) -> Self {
        Self::new(
            path,
            MapLoader {
                map: LoaderFunction::Fn(map),
                _types: PhantomData,
            },
        )
    }
}

impl<Loader> Deref for StaticWatchFile<Loader>
where
    Loader: WatchFileLoader,
{
    type Target = WatchFile<Loader>;

    fn deref(&self) -> &Self::Target {
        self.file.get_or_init(|| {
            let (path, loader) = self
                .init
                .lock()
                .expect("poison impossible")
                .take()
                .expect("OnceLock prevents multiple calls");
            WatchFile::try_new(Path::new(path), loader)
        })
    }
}

/// A [`WatchFileLoader`] implementation that returns the contents of the file
/// as a `Vec<u8>`.
#[derive(Debug)]
pub struct FileContents;

impl WatchFileLoader for FileContents {
    type Contents = Vec<u8>;

    type Error = Infallible;

    fn load(&mut self, data: &[u8]) -> Result<Self::Contents, Self::Error> {
        Ok(data.to_vec())
    }
}

#[cfg(test)]
mod tests;
