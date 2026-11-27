# Decremental (1+eps)-SSSP in weighted digraphs: adaptive distance queries and near-optimal dense bounds

Let $G$ be a directed graph with $n$ vertices, $m$ edges and aspect ratio $W$, undergoing edge deletions, with source $s$ and $\varepsilon > 0$.

1. (Probst Gutenberg-Wulff-Nilsen) There is a Las Vegas $(1+\varepsilon)$-approximate decremental SSSP data structure, robust to adversaries that adapt to the returned distance estimates (but not to returned paths), with total expected update time $\tilde O(m^{2/3}n^{4/3})$ on unweighted graphs and $\tilde O(m^{3/4}n^{5/4}\log W)$ on weighted graphs; assuming an oblivious adversary, $\tilde O(\sqrt{m}\,n^{3/2})$ and $\tilde O(m^{2/3}n^{4/3}\log W)$ respectively.
2. (Bernstein-Probst Gutenberg-Wulff-Nilsen) There is a randomized $(1+\varepsilon)$-approximate decremental SSSP data structure against an oblivious adversary whose estimates are correct with high probability at every stage, with total expected update time $\tilde O(n^2\log^4 W/\varepsilon)$, near-optimal for dense graphs with polynomial weights, and $\tilde O(m n^{2/3}\log^3 W/\varepsilon)$ for sparse graphs, with $O(1)$ distance queries and path queries in time $O(|P|)$.

## Proof sketch

Both use approximate topological orders: the vertices are partitioned into low-diameter strongly connected pieces arranged in an order that is acyclic up to short backward detours. Within a piece, distances are approximated by its small diameter, while across pieces the graph behaves like a DAG, for which decremental SSSP is easier. The second result introduces a more powerful abstraction of such orders and a new core subroutine, which reduces decremental SSSP in general digraphs to the DAG case and achieves near-quadratic total time.

## Depends on

- [Decremental (1+eps)-approximate single-source shortest paths](decremental-approximate-sssp-problem.md)
- [Oblivious and adaptive adversaries; amortized and worst-case update time](../../../data-structures/disjoint-sets-and-dynamic-trees/fully-dynamic-connectivity-and-spanning-forests/adversary-and-update-time-models.md)

## Sources

- Maximilian Probst Gutenberg, Christian Wulff-Nilsen, "Decremental SSSP in Weighted Digraphs: Faster and Against an Adaptive Adversary", SODA (2020), arXiv:2001.10821.
- Aaron Bernstein, Maximilian Probst Gutenberg, Christian Wulff-Nilsen, "Near-Optimal Decremental SSSP in Dense Weighted Digraphs", FOCS (2020), arXiv:2004.04496.
