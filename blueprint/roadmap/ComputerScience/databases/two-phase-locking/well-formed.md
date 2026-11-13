# Well-formed locked schedules

A locked schedule $s$ (a list of reads, writes, lock
requests and lock releases of transactions) is well formed when its accesses are covered by
locks and it releases its locks: every read or write in $s$ is preceded by a lock request of its
own transaction on its item, in a mode covering the access (shared or exclusive for a read,
exclusive for a write), with no release of that item by that transaction in between; and every
lock request in $s$ by a transaction on an item is followed later in $s$ by a release of that
item by the same transaction.
