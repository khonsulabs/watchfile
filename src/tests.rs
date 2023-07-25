use std::fs;
use std::io::Write;
use std::path::Path;
use std::sync::{Condvar, Mutex, MutexGuard, PoisonError};
use std::time::Duration;

use crate::{global_state, StaticWatchFile, WatchFile};

/// Tests that the global state is cleaned up after installing a watcher. This
/// test doesn't verify the watcher installation actually does anything, just
/// that after the watcher is dropped the state is clear.
///
/// This test must be completed before any other test, otherwise the state may
/// not actually end up being cleared. For example, any test involving the
/// static file watcher will leave a file entry perpetually.
#[test]
fn cleanup() {
    let _guard = CleanupGuard::default();

    let file = tempfile::NamedTempFile::new().unwrap();
    let watcher = WatchFile::watch(file.path()).unwrap();
    drop(watcher);
    drop(file);

    let global = global_state();
    assert!(global.watchers.is_empty());
}

static CLEANUP_GUARD: Mutex<bool> = Mutex::new(false);
static CLEANUP_SYNC: Condvar = Condvar::new();

fn wait_for_cleanup_test_to_complete() {
    let mut guard = CLEANUP_GUARD
        .lock()
        .map_or_else(PoisonError::into_inner, |g| g);
    while !*guard {
        let (g, result) = CLEANUP_SYNC
            .wait_timeout(guard, Duration::from_millis(300))
            .map_or_else(PoisonError::into_inner, |g| g);
        guard = g;
        if result.timed_out() {
            println!("Cleanup test did not complete. Proceeding test.");
            return;
        }
    }
}

struct CleanupGuard(MutexGuard<'static, bool>);

impl Default for CleanupGuard {
    fn default() -> Self {
        Self(
            CLEANUP_GUARD
                .lock()
                .map_or_else(PoisonError::into_inner, |g| g),
        )
    }
}

impl Drop for CleanupGuard {
    fn drop(&mut self) {
        *self.0 = true;
        CLEANUP_SYNC.notify_all();
    }
}

#[test]
fn basic() {
    wait_for_cleanup_test_to_complete();

    let mut file = tempfile::NamedTempFile::new().unwrap();
    let mut watcher = WatchFile::watch(file.path()).unwrap();
    assert_eq!(*watcher.read_contents().unwrap(), b"");
    file.write_all(b"hello, world!").unwrap();
    file.as_file().sync_all().unwrap();
    watcher
        .watch_timeout(std::time::Duration::from_secs(1))
        .unwrap();
    assert_eq!(*watcher.read_contents().unwrap(), b"hello, world!");
}

#[test]
fn static_watch_file() {
    static TEST: StaticWatchFile = StaticWatchFile::watch("static-test-file");
    wait_for_cleanup_test_to_complete();

    let path = Path::new("static-test-file");
    if path.exists() {
        fs::remove_file(path).unwrap();
    }

    // Static files don't really have a good way to watch unless you justf clone
    // them. This is because the read state requires mut access.
    TEST.mark_read();

    // Watch for the file creation
    let mut file = fs::OpenOptions::new()
        .create(true)
        .write(true)
        .open(path)
        .unwrap();
    file.write_all(b"hello").unwrap();
    file.sync_all().unwrap();

    TEST.watch_timeout(std::time::Duration::from_secs(1))
        .unwrap();
    assert_eq!(*TEST.contents().unwrap(), b"hello");

    file.write_all(b", world!").unwrap();
    file.sync_all().unwrap();
    TEST.watch_timeout(std::time::Duration::from_secs(1))
        .unwrap();
    assert_eq!(*TEST.contents().unwrap(), b"hello, world!");
    drop(file);
    fs::remove_file(path).unwrap();
}
