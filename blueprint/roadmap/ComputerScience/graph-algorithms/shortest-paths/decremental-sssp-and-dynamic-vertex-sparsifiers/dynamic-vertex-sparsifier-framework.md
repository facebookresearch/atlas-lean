# Chen-Goranci-Henzinger-Peng-Saranurak: dynamic cuts, distances and resistances via vertex sparsifiers

For undirected graphs with $n$ vertices and $m$ edges, the vertex-sparsifier framework gives the following. Except for the incremental shortest-path structure, which is deterministic, the algorithms are randomized, answer correctly with high probability, and, unless stated otherwise, assume an oblivious adversary.

1. For capacity ratio $\mathrm{poly}(n)$, a fully dynamic algorithm returning $\tilde O(\log n)$-approximate maximum-flow / minimum-cut values between query pairs $s, t$ in $O(m^{2/3}\log^7 n)$ amortized update time and $\tilde O(m^{2/3})$ query time; for polynomially bounded capacities and against an adaptive adversary, in $\tilde O(m^{3/4})$ amortized update and query time.
2. For all integers $\ell, r \ge 1$ and some constant $c > 0$, an incremental all-pairs shortest-path structure on weighted graphs maintaining $(2r-1)^\ell$-approximate distances in $O(\ell c^{\ell-1} r^\ell m^{1/(\ell+1)} n^{\ell/r}\log^{\ell-1} n)$ worst-case update time and $\ell$ times that worst-case query time, so that stretch is traded against time; and a fully dynamic structure returning $\tilde O(\log n)$-approximate distances between query pairs in $O(n^{2/3+o(1)})$ amortized update and query time.
3. For every integer $d \ge 1$, $\varepsilon \in (0, 1)$ and weight ratio $\mathrm{poly}(n)$, a fully dynamic algorithm returning $(1 + 2d\varepsilon)$-approximate effective resistances between query pairs in $O(n^{2/3+1/(3d+3)}\varepsilon^{-(2d+4)}\log^{2d+11} n)$ amortized update time and $O(n^{2/3+1/(3d+3)}\varepsilon^{-(2d+2)}\log^{9d+10} n)$ query time.

## Proof sketch

Any problem admitting vertex sparsifiers, small graphs on a terminal set that preserve the quantity of interest between terminals, can be made dynamic: keep a hierarchy of sparsifiers on random terminal sets, add update endpoints and query vertices as terminals, and rebuild levels periodically while tracking recourse between levels. Cuts use a dynamic version of Madry's $j$-tree decomposition, distances adapt Thorup-Zwick distance oracles, and resistances use the random-walk spectral vertex sparsifier hierarchically. Balancing rebuild periods against sparsifier size gives the $n^{2/3}$-type bounds.

## Depends on

- [Schur complements of graph Laplacians onto terminal sets and spectral vertex sparsifiers](laplacian-schur-complement-onto-terminals.md)
- [Oblivious and adaptive adversaries; amortized and worst-case update time](../../../data-structures/disjoint-sets-and-dynamic-trees/fully-dynamic-connectivity-and-spanning-forests/adversary-and-update-time-models.md)
- [Minimum cut size](../../../randomized-algorithms/karger-s-algorithm/is-min-cut.md)
- [Effective resistance](../../../../GraphTheory/algebraic-graph-theory/part-01/effective-resistance-and-electrical-networks/effective-resistance.md)

## Proof depends on

- [Max-flow min-cut theorem](../../../../GraphTheory/matchings-and-flows/max-flow-min-cut-theorem/max-flow-min-cut.md)
- [Durfee-Gao-Goranci-Peng: fully dynamic spectral vertex sparsifiers and all-pairs effective resistances](dynamic-spectral-vertex-sparsifiers.md)

## Sources

- Li Chen, Gramoz Goranci, Monika Henzinger, Richard Peng, Thatchaphol Saranurak, "Fast Dynamic Cuts, Distances and Effective Resistances via Vertex Sparsifiers", FOCS (2020), arXiv:2005.02368.
- David Durfee, Yu Gao, Gramoz Goranci, Richard Peng, "Fully Dynamic Spectral Vertex Sparsifiers and Applications", STOC (2019), arXiv:1906.10530.
