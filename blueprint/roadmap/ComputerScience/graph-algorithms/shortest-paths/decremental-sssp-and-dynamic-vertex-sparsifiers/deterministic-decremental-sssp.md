# Deterministic (1+eps)-approximate decremental SSSP in almost-linear total update time

For undirected graphs with $m$ edges and integer weights in $[1, W]$ with $W \le n^{O(1)}$, there is a deterministic decremental $(1+\varepsilon)$-approximate SSSP data structure with total update time $m^{1 + o(1)}$; being deterministic, it works against adaptive adversaries (Bernstein-Probst Gutenberg-Saranurak). As a consequence, $(1-\varepsilon)$-approximate min-cost flow in undirected graphs with capacities and costs on edges and vertices is solvable in almost-linear time. This completes a line of deterministic results: $\tilde O(n^2)$ total time for unweighted undirected graphs (Bernstein-Chechik) and $O(n^{2+o(1)})$ total time on weighted undirected graphs with path queries in time $O(|P| \cdot n^{o(1)})$ (Chuzhoy-Saranurak); for directed graphs, deterministic decremental single-source reachability and SCC in $m n^{2/3 + o(1)}$ and SSSP in $n^{2 + 2/3 + o(1)}$ total time (Bernstein-Probst Gutenberg-Saranurak).

## Proof sketch

The key technique treats low-diameter subgraphs like expanders: a covering of the graph by low-diameter pieces is maintained deterministically, and inside each piece short paths are found as in an expander, while deletions are absorbed by pruning-type arguments instead of a static expander decomposition. Even-Shiloach trees run on a sparse emulator over the piece centres, rounded to $n^{o(1)}$ distance scales. For min-cost flow, randomization breaks the flow-decomposition barrier inside multiplicative-weight updates, and the adaptive decremental SSSP oracle supplies the shortest paths.

## Depends on

- [Decremental (1+eps)-approximate single-source shortest paths](decremental-approximate-sssp-problem.md)
- [Oblivious and adaptive adversaries; amortized and worst-case update time](../../../data-structures/disjoint-sets-and-dynamic-trees/fully-dynamic-connectivity-and-spanning-forests/adversary-and-update-time-models.md)

## Proof depends on

- [Saranurak-Wang expander pruning under online edge deletions](../../../../GraphTheory/graph-families-and-operations/expander-decomposition-and-pruning/expander-pruning-theorem.md)
- [Saranurak-Wang near-linear-time strong expander decomposition](../../../../GraphTheory/graph-families-and-operations/expander-decomposition-and-pruning/saranurak-wang-expander-decomposition.md)
- [Even-Shiloach: exact decremental BFS trees in O(mD) total update time](even-shiloach-total-time.md)

## Sources

- Aaron Bernstein, Maximilian Probst Gutenberg, Thatchaphol Saranurak, "Deterministic Decremental SSSP and Approximate Min-Cost Flow in Almost-Linear Time", FOCS (2021), arXiv:2101.07149.
- Aaron Bernstein, Shiri Chechik, "Deterministic Decremental Single Source Shortest Paths: Beyond the O(mn) Bound", STOC (2016).
- Julia Chuzhoy, Thatchaphol Saranurak, "Deterministic Algorithms for Decremental Shortest Paths via Layered Core Decomposition", SODA (2021), arXiv:2009.08479.
- Aaron Bernstein, Maximilian Probst Gutenberg, Thatchaphol Saranurak, "Deterministic Decremental Reachability, SCC, and Shortest Paths via Directed Expanders and Congestion Balancing", FOCS (2020), arXiv:2009.02584.
