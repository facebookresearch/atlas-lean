# Graveyard hashing eliminates primary clustering

For graveyard hashing with a uniformly random hash function and any sequence of insertions, deletions and queries that is oblivious to the hash function, if an operation is performed while the current load factor is $1 - 1/x$ (with $x \ge 2$), then its expected amortized cost is $O(x)$. By the spread-free-slots lemma, $\Omega(x)$ is necessary for insertions in any linear-probing layout at that load factor, so graveyard hashing is asymptotically optimal among linear-probing tables.

## Proof sketch

Planted tombstones guarantee that every window of $\Theta(x)$ hash positions contains a reusable slot right after a rebuild, which caps the length of runs that insertions must traverse; the subsequent $\Theta(n/x)$ operations can consume only a constant fraction of the planted tombstones in expectation, so the cap persists until the next rebuild. Combining this with the anti-clustering analysis bounds the expected scan length by $O(x)$, and rebuild cost is $O(n)$ per $\Theta(n/x)$ operations.

## Depends on

- [Graveyard hashing](graveyard-hashing.md)
- [Tombstones defeat primary clustering under hovering workloads](tombstones-anticluster-hovering-workloads.md)
- [Even perfectly spread free slots force $\Omega(x)$ scan length](spread-free-slots-force-linear-cost.md)

## Proof depends on

- [Graveyard hashing](graveyard-hashing.md)
- [Tombstones defeat primary clustering under hovering workloads](tombstones-anticluster-hovering-workloads.md)
- [Even perfectly spread free slots force $\Omega(x)$ scan length](spread-free-slots-force-linear-cost.md)

## Sources

- Michael A. Bender, Bradley C. Kuszmaul, William Kuszmaul, "Linear Probing Revisited: Tombstones Mark the Demise of Primary Clustering", FOCS (2021), arXiv:2107.01250.
