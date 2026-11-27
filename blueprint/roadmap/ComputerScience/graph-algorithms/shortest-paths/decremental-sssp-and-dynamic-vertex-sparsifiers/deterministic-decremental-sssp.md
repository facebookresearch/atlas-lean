# Deterministic (1+eps)-approximate decremental SSSP in almost-linear total update time

For undirected graphs $G = (V, E, w)$ with $m$ edges and aspect ratio $W$, a source $s$ and any $\varepsilon > 1/\mathrm{polylog}(n)$, there is a deterministic decremental $(1+\varepsilon)$-approximate SSSP data structure that maintains the distance estimates explicitly in total update time $m^{1 + o(1)}\,\mathrm{polylog}(W)$ and answers $(1+\varepsilon)$-approximate shortest $s$-$t$ path queries in time $|\pi(s,t)|\,n^{o(1)}$; being deterministic, it works against adaptive adversaries (Bernstein-Probst Gutenberg-Saranurak). As a consequence, for $\varepsilon > 1/\mathrm{polylog}(n)$, $(1+\varepsilon)$-approximate min-cost flow in undirected graphs with capacities and costs on edges and vertices is solvable in almost-linear time. This completes a line of deterministic results: $\tilde O(n^2)$ total time for unweighted undirected graphs (Bernstein-Chechik) and $n^{2+o(1)}\log^2 L/\varepsilon^2$ total time on weighted undirected graphs with largest-to-smallest weight ratio $L$, with path queries in time $O(|P| \cdot n^{o(1)})$ (Chuzhoy-Saranurak); for directed graphs, deterministic decremental single-source reachability and SCC in $m n^{2/3 + o(1)}$ and $(1+\varepsilon)$-approximate SSSP in $n^{2 + 2/3 + o(1)}\log W/\varepsilon$ total time (Bernstein-Probst Gutenberg-Saranurak).

## Proof sketch

The key technique treats low-diameter subgraphs like expanders: a covering of the graph by low-diameter pieces is maintained deterministically, and inside each piece short paths are found as in an expander, while deletions are absorbed by pruning-type arguments instead of a static expander decomposition. Even-Shiloach trees run to hop depth $h$ on an $(h, \varepsilon)$-emulator built from the pieces, one per distance scale. For min-cost flow, randomization breaks the flow-decomposition barrier inside multiplicative-weight updates, and the adaptive decremental SSSP oracle supplies the shortest paths.

## Depends on

- [Decremental (1+eps)-approximate single-source shortest paths](decremental-approximate-sssp-problem.md)
- [Oblivious and adaptive adversaries; amortized and worst-case update time](../../../data-structures/disjoint-sets-and-dynamic-trees/fully-dynamic-connectivity-and-spanning-forests/adversary-and-update-time-models.md)

## Proof depends on

- [Saranurak-Wang expander pruning under online edge deletions](../../../../GraphTheory/graph-families-and-operations/expander-decomposition-and-pruning/expander-pruning-theorem.md)
- [Even-Shiloach: exact decremental BFS trees in O(mD) total update time](even-shiloach-total-time.md)

## Sources

- Aaron Bernstein, Maximilian Probst Gutenberg, Thatchaphol Saranurak, "Deterministic Decremental SSSP and Approximate Min-Cost Flow in Almost-Linear Time", FOCS (2021), arXiv:2101.07149.
- Aaron Bernstein, Shiri Chechik, "Deterministic Decremental Single Source Shortest Paths: Beyond the O(mn) Bound", STOC (2016).
- Julia Chuzhoy, Thatchaphol Saranurak, "Deterministic Algorithms for Decremental Shortest Paths via Layered Core Decomposition", SODA (2021), arXiv:2009.08479.
- Aaron Bernstein, Maximilian Probst Gutenberg, Thatchaphol Saranurak, "Deterministic Decremental Reachability, SCC, and Shortest Paths via Directed Expanders and Congestion Balancing", FOCS (2020), arXiv:2009.02584.
