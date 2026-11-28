# Graveyard hashing eliminates primary clustering

For graveyard hashing with a uniformly random hash function and any sequence of insertions, deletions and queries that is oblivious to the hash function, if an insertion, query or deletion is performed while the current load factor is $1 - 1/x$ (with $x \ge 2$), then it takes expected time $O(x)$ and incurs amortized time $O(x)$ for rebuilds (Theorem 3), even in insertion-only workloads. By the spread-free-slots lemma, $\Omega(x)$ is necessary for insertions in any linear-probing layout at that load factor, so graveyard hashing is asymptotically optimal among linear-probing tables.

## Proof sketch

Right after a rebuild every window of $2x$ consecutive hashes holds a planted tombstone, which caps the length of runs that insertions must traverse; at most $n/(4x)$ insertions occur before the next rebuild, while $n/(2x)$ tombstones were planted, so reusable slots stay plentiful throughout the window. Combining this with the anti-clustering analysis bounds the expected scan length by $O(x)$, and rebuild cost is $O(n)$ per $\Theta(n/x)$ operations.

## Depends on

- [Graveyard hashing](graveyard-hashing.md)

## Proof depends on

- [Tombstones defeat primary clustering under hovering workloads](tombstones-anticluster-hovering-workloads.md)
- [Even perfectly spread free slots force $\Omega(x)$ scan length](spread-free-slots-force-linear-cost.md)

## Sources

- Michael A. Bender, Bradley C. Kuszmaul, William Kuszmaul, "Linear Probing Revisited: Tombstones Mark the Demise of Primary Clustering", FOCS (2021), arXiv:2107.01250.
