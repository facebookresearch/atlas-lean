# Minimum-weight outgoing edges of a vertex set

Let $G$ be a finite connected simple graph with edge weights $w : E(G) \to \mathbb{R}$. For a nonempty proper vertex subset $S$ (a **fragment**), an edge $e = uv$ with $u \in S$, $v \notin S$ is a **minimum-weight outgoing edge (MOE)** of $S$ if $w(e) \le w(e')$ for every edge $e'$ with exactly one endpoint in $S$. A **minimum spanning tree (MST)** is a spanning tree minimizing total weight.

## Depends on

- [Spanning tree](../../../../GraphTheory/algebraic-graph-theory/part-01/kirchhoff-s-matrix-tree-theorem/is-spanning-tree.md)
- [Kruskal's algorithm gives a minimum spanning forest](../kruskal-s-algorithm/kruskal-minimal.md)

## Sources

- R. G. Gallager, P. A. Humblet and P. M. Spira, "A Distributed Algorithm for Minimum-Weight Spanning Trees", ACM Transactions on Programming Languages and Systems 5(1), 1983.
- R. E. Tarjan, "Data Structures and Network Algorithms", SIAM, 1983.
