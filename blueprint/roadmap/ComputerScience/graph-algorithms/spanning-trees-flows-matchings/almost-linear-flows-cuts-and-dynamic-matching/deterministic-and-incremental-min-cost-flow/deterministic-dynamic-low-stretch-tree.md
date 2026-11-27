# Deterministic fully dynamic low-stretch spanning trees with subpolynomial update time

There is a deterministic data structure that, given a dynamic $n$-vertex graph undergoing insertions and deletions of edges with integral lengths bounded by $\exp(\log^{O(1)} n)$, maintains a spanning tree of average stretch $n^{o(1)}$ in worst-case $n^{o(1)}$ time per update. The tree is kept in memory with $n^{o(1)}$ amortized recourse per update, and the changes can be output explicitly in amortized $n^{o(1)}$ time per update.

## Proof sketch

Use one tree chain built from dynamic low-stretch forests and the deterministic dynamic spanner, with gradients ignored: the stretch of an edge in the induced tree is the product of the per-level stretch overestimates and spanner path lengths, which is $\widetilde{O}(1)^d\gamma_s^d = n^{o(1)}$ on average. Edge insertions are given stretch $1$ by making their endpoints roots, length classes are handled by bucketing into $\log^{O(1)} n$ scales, and rebuilds of level $i$ every $m/k^i$ updates are deamortized by maintaining two copies.

## Depends on

- [Edge stretch with respect to a spanning tree and edge lengths](../dynamic-min-ratio-cycle-data-structures/edge-stretch-wrt-spanning-tree.md)

## Proof depends on

- [Dynamic low-stretch forests with stable stretch overestimates](../dynamic-min-ratio-cycle-data-structures/dynamic-low-stretch-forest.md)
- [Deterministic dynamic spanners with low-recourse short embeddings under deletions and vertex splits](../dynamic-min-ratio-cycle-data-structures/deterministic-dynamic-spanner-embedding.md)
- [Tree chains with shifts and rebuilds over recursive sparsified core graphs](../dynamic-min-ratio-cycle-data-structures/shifted-tree-chain.md)

## Sources

- Jan van den Brand, Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, Aaron Sidford, "A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow", FOCS (2023), arXiv:2309.16629.
