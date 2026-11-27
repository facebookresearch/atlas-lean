# Deterministic fully dynamic low-stretch spanning trees with subpolynomial update time

There is a deterministic data structure that, given a dynamic $n$-vertex graph that stays connected after every update, undergoing insertions and deletions of edges with positive integral lengths bounded by $\exp(\log^{O(1)} n)$, maintains a spanning tree of average stretch $n^{o(1)}$ in worst-case $n^{o(1)}$ time per update. Connectivity is needed for a spanning tree to exist, since deleting a bridge leaves none, and positive lengths make the stretch well defined. The tree is kept in memory with $n^{o(1)}$ amortized recourse per update, and the changes can be output explicitly in amortized $n^{o(1)}$ time per update.

## Proof sketch

Use a hierarchy of $d = \log^{1/18} m$ levels with $k = m^{1/d}$: at each level maintain a dynamic low-stretch forest with unit weights, contract it, split the contracted edges into $\widetilde{O}(1)$ buckets by stretch overestimate and length, and replace each bucket by a deterministic spanner with a low-congestion embedding. The union of the forests is the tree. Charging stretch through the forest routing and the spanner embeddings loses a factor $O(k\gamma_c)$ per level with $\gamma_c = \exp(O(\log^{8/9} m\log\log m))$, so the total stretch is $m^{1+o(1)}$. Edge insertions are given stretch $1$ by making their endpoints roots, levels $i, \ldots, d-1$ are rebuilt once level $i$ has received $m/k^{i+1}$ updates, and the amortized bounds are deamortized by standard batching.

## Depends on

- [Edge stretch with respect to a spanning tree and edge lengths](../dynamic-min-ratio-cycle-data-structures/edge-stretch-wrt-spanning-tree.md)

## Proof depends on

- [Dynamic low-stretch forests with stable stretch overestimates](../dynamic-min-ratio-cycle-data-structures/dynamic-low-stretch-forest.md)
- [Deterministic dynamic spanners with low-recourse short embeddings under deletions and vertex splits](../dynamic-min-ratio-cycle-data-structures/deterministic-dynamic-spanner-embedding.md)
- [Tree chains with shifts and rebuilds over recursive sparsified core graphs](../dynamic-min-ratio-cycle-data-structures/shifted-tree-chain.md)

## Sources

- Jan van den Brand, Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, Aaron Sidford, "A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow", FOCS (2023), arXiv:2309.16629.
