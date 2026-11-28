# Linear probing with tombstones and periodic rebuilds

A *linear-probing table with tombstones* stores keys in $n$ circular slots using a hash function $h$; a slot is free, holds a key, or holds a *tombstone*. A query for $u$ scans $h(u), h(u)+1, \dots$ (mod $n$) until it finds $u$ or a free slot, treating tombstones as non-matching. A deletion of $u$ replaces $u$ by a tombstone. An insertion of $u$ scans from $h(u)$ and stores $u$ in the first slot that is free or holds a tombstone. Every $R$ insertions the table is *rebuilt*: all tombstones are removed and the keys are reinserted; classically $R = n/(2x)$ at load factor $1 - 1/x$, so that tombstones cannot affect the asymptotic load factor. A workload *hovers at load factor $1 - 1/x$* if it alternates insertions and deletions on a table holding $(1 - 1/x)n$ keys.

## Depends on

- [Linear-probing probe sequence](../open-addressing/linear-probe.md)

## Sources

- Michael A. Bender, Bradley C. Kuszmaul, William Kuszmaul, "Linear Probing Revisited: Tombstones Mark the Demise of Primary Clustering", FOCS (2021), arXiv:2107.01250.
- Donald E. Knuth, "The Art of Computer Programming, Volume 3: Sorting and Searching", 2nd ed., Addison-Wesley (1998).
