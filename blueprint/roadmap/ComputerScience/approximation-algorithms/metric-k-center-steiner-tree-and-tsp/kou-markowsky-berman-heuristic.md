# The Kou-Markowsky-Berman heuristic for Steiner tree in graphs

For an edge-weighted connected graph $G$ with nonnegative weights and terminal set $R$, the **metric completion** on $R$ assigns to each pair of terminals the shortest-path distance in $G$. The **Kou-Markowsky-Berman heuristic** computes a minimum spanning tree of the metric completion and replaces each tree edge by the edges of a shortest path in $G$; the resulting subgraph connects $R$ and has total weight at most twice the optimum Steiner tree weight in $G$, even though $G$'s weights need not satisfy the triangle inequality.

## Proof sketch

Shortest-path distances form a metric, so the metric bound applies to the completion; expanding paths does not increase total weight, and the optimum in $G$ dominates the optimum in the completion.

## Depends on

- [Steiner tree instances](../../../TheoryOfComputation/np-completeness/paths-cycles-and-subgraphs/steiner-tree/steiner-tree-instance.md)

## Proof depends on

- [The terminal MST is a 2-approximation for metric Steiner tree](metric-steiner-tree-mst-two-approximation.md)

## Sources

- L. Kou, G. Markowsky and L. Berman, "A Fast Algorithm for Steiner Trees", Acta Informatica 15, 1981.
- D. P. Williamson and D. B. Shmoys, "The Design of Approximation Algorithms", Cambridge University Press, 2011.
