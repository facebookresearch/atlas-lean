# Tombstones defeat primary clustering under hovering workloads

Consider ordered linear probing with tombstones under a hovering workload at load factor $1 - 1/x$, with uniformly random hashing, where insertions and deletions are oblivious to the hash function and the table is rebuilt every $R = \Theta(n/x)$ operations. Then the amortized expected cost of an insertion is $x \cdot (\log x)^{O(1)}$, rather than the $\Theta(x^2)$ cost of insertion-only linear probing at the same load factor.

## Proof sketch

Deletions leave tombstones at hash-random positions, so between rebuilds the tombstones form an approximately uniformly spread set of reusable slots. An insertion that lands in a long run is likely to meet a tombstone after scanning $\tilde{O}(x)$ slots, and the analysis tracks the run lengths through a sequence of phases showing that the anti-clustering effect of tombstones dominates the clustering effect of insertions when insertions and deletions are one-for-one. Rebuilding every $\Theta(n/x)$ operations amortizes to $O(x)$ per operation.

## Depends on

- [Ordered linear probing](ordered-linear-probing.md)
- [Primary clustering: insertion-only linear probing costs $\Theta(x^2)$](primary-clustering-quadratic-cost.md)

## Proof depends on

- [Ordered linear probing](ordered-linear-probing.md)
- [Primary clustering: insertion-only linear probing costs $\Theta(x^2)$](primary-clustering-quadratic-cost.md)

## Sources

- Michael A. Bender, Bradley C. Kuszmaul, William Kuszmaul, "Linear Probing Revisited: Tombstones Mark the Demise of Primary Clustering", FOCS (2021), arXiv:2107.01250.
