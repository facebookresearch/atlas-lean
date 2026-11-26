# Chen-Goranci-Henzinger-Peng-Saranurak: dynamic cuts, distances and resistances via vertex sparsifiers

For undirected graphs with $n$ vertices and $m$ edges, the vertex-sparsifier framework gives:

1. a fully dynamic algorithm approximating all-pairs maximum flow and minimum cut values within a nearly logarithmic factor in $\tilde O(n^{2/3})$ amortized time per operation against an oblivious adversary, and in $\tilde O(m^{3/4})$ time against an adaptive adversary;
2. an incremental data structure maintaining $O(1)$-approximate shortest paths in $n^{o(1)}$ time per operation, and fully dynamic approximate all-pairs shortest paths and transshipment in $\tilde O(n^{2/3 + o(1)})$ amortized time per operation;
3. a fully dynamic algorithm approximating all-pairs effective resistances within $1 + \varepsilon$ in $\tilde O(n^{2/3 + o(1)}\varepsilon^{-O(1)})$ amortized update time.

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
