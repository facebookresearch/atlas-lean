# Schedules covered by locks

A locked schedule $s$ is covered by locks when every read or
write is protected by a lock of its transaction: whenever $s$ has at position $p$ a read or write
$o$ by transaction $t$ on item $x$, just before position $p$ transaction $t$ holds a lock on $x$
(acquired at an earlier position and not released since) whose mode covers the mode $o$ requires,
namely shared for a read and exclusive for a write; an exclusive lock covers both modes.
