# Chuzhoy-Khanna: vertex-decremental SSSP against an adaptive adversary and vertex-capacitated flow

For an undirected graph with $n$ vertices and edge lengths $\ell(e) \ge 1$ bounded by $L$, undergoing vertex deletions, there is a randomized $(1+\varepsilon)$-approximate SSSP data structure working against an adaptive adversary, with total expected update time $O(n^{2 + o(1)}\log L)$ and expected time $O(n\log L)$ per shortest-path query, which returns an $s$-$v$ path of length at most $(1+\varepsilon)$ times the shortest. Consequently, $(1+\varepsilon)$-approximate maximum $s$-$t$ flow and minimum $s$-$t$ cut in vertex-capacitated undirected graphs can be computed in expected time $n^{2 + o(1)}$, and an $O(\log^4 n)$-approximation for vertex sparsest cut in expected time $n^{2+o(1)}$.

## Proof sketch

The main ingredient is a core decomposition of a dense graph computed in time $\tilde O(|E(G)| + n^{1+o(1)})$: the graph is split into well-connected cores in which any two vertices are joined by short paths that survive many adaptive deletions, plus a sparse remainder handled by Even-Shiloach trees. Queries route through cores using their expansion, so returned paths reveal no exploitable randomness. The flow results follow by running multiplicative-weights over vertex lengths, where each iteration needs one approximate shortest path in a vertex-decremental graph, which is exactly why adaptive path queries are needed.

## Depends on

- [Decremental (1+eps)-approximate single-source shortest paths](decremental-approximate-sssp-problem.md)
- [Oblivious and adaptive adversaries; amortized and worst-case update time](../../../data-structures/disjoint-sets-and-dynamic-trees/fully-dynamic-connectivity-and-spanning-forests/adversary-and-update-time-models.md)

## Proof depends on

- [Max-flow min-cut theorem](../../../../GraphTheory/matchings-and-flows/max-flow-min-cut-theorem/max-flow-min-cut.md)
- [Cut conductance, phi-expanders and degree-preserving induced subgraphs](../../../../GraphTheory/graph-families-and-operations/expander-decomposition-and-pruning/conductance-and-phi-expanders.md)
- [Even-Shiloach: exact decremental BFS trees in O(mD) total update time](even-shiloach-total-time.md)

## Sources

- Julia Chuzhoy, Sanjeev Khanna, "A New Algorithm for Decremental Single-Source Shortest Paths with Applications to Vertex-Capacitated Flow and Cut Problems", STOC (2019), arXiv:1905.11512.
