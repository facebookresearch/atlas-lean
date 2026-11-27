# Chuzhoy-Khanna: vertex-decremental SSSP against an adaptive adversary and vertex-capacitated flow

For a simple undirected graph with $n$ vertices and edge lengths $\ell(e) > 0$ whose largest-to-smallest ratio is $L$, undergoing vertex deletions, a source $s$ and $0 < \varepsilon < 1$, there is a randomized Las Vegas $(1+\varepsilon)$-approximate SSSP data structure working against an adaptive adversary, with total expected update time $O(n^{2 + o(1)}\log^3(1/\varepsilon)\log L/\varepsilon^2)$ and expected time $O(n\,\mathrm{poly}\log n\,\log L\,\log(1/\varepsilon))$ per shortest-path query, which returns an $s$-$v$ path, if one exists, of length at most $(1+\varepsilon)$ times the shortest. Here and below $\log L$ and $\log(1/\varepsilon)$ are read as $\max\{1, \log L\}$ and $\max\{1, \log(1/\varepsilon)\}$, so the bounds do not vanish at $L = 1$ or for $\varepsilon$ close to $1$. For fixed $\varepsilon$ this is total time $O(n^{2+o(1)}\log L)$ and query time $\tilde O(n\log L)$. Consequently, for fixed $\varepsilon$, $(1+\varepsilon)$-approximate maximum $s$-$t$ flow and minimum $s$-$t$ cut in vertex-capacitated undirected graphs can be computed in expected time $n^{2 + o(1)}$, and an $O(\log^4 n)$-approximation for vertex sparsest cut in expected time $n^{2+o(1)}$.

## Proof sketch

The main ingredient is a core decomposition of a dense graph computed in time $\tilde O(|E(G)| + n^{1+o(1)})$: the graph is split into well-connected cores in which any two vertices are joined by short paths that survive many adaptive deletions, while the rest of the graph is handled by Even-Shiloach trees on a contracted graph. Queries route through cores using their expansion, and the cores keep short paths after many adaptive deletions, so the guarantee does not rely on hiding random choices. The flow results follow by running multiplicative-weights over vertex lengths, where each iteration needs one approximate shortest path in a vertex-decremental graph, which is exactly why adaptive path queries are needed.

## Depends on

- [Decremental (1+eps)-approximate single-source shortest paths](decremental-approximate-sssp-problem.md)
- [Oblivious and adaptive adversaries; amortized and worst-case update time](../../../data-structures/disjoint-sets-and-dynamic-trees/fully-dynamic-connectivity-and-spanning-forests/adversary-and-update-time-models.md)

## Proof depends on

- [Max-flow min-cut theorem](../../../../GraphTheory/matchings-and-flows/max-flow-min-cut-theorem/max-flow-min-cut.md)
- [Cut conductance, phi-expanders and degree-preserving induced subgraphs](../../../../GraphTheory/graph-families-and-operations/expander-decomposition-and-pruning/conductance-and-phi-expanders.md)
- [Even-Shiloach: exact decremental BFS trees in O(mD) total update time](even-shiloach-total-time.md)

## Sources

- Julia Chuzhoy, Sanjeev Khanna, "A New Algorithm for Decremental Single-Source Shortest Paths with Applications to Vertex-Capacitated Flow and Cut Problems", STOC (2019), arXiv:1905.11512.
