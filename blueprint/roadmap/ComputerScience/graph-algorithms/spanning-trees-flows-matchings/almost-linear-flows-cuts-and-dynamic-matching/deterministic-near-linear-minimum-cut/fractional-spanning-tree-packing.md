# Fractional spanning tree packings and the packing value

Let $G = (V, E, w)$ be a connected undirected graph with $|V| \ge 2$ and positive weights and let $\mathcal{T}$ be the set of its spanning trees. A *tree packing* is a function $y : \mathcal{T} \to \mathbb{R}_{\ge 0}$ such that

$$
\sum_{T \in \mathcal{T} \,:\, e \in E(T)} y_T \le w(e) \quad \text{for every } e \in E.
$$

Its *value* is $\sum_{T} y_T$, and the *packing number* $\tau(G)$ is the maximum value of a tree packing; it is finite and attained because $|V| \ge 2$ gives every spanning tree an edge, whereas for $|V| = 1$ the edgeless tree could carry unbounded weight. For unweighted multigraphs an integral packing is a family of edge-disjoint spanning trees.

## Depends on

- [Spanning tree](../../../../../GraphTheory/algebraic-graph-theory/part-01/kirchhoff-s-matrix-tree-theorem/is-spanning-tree.md)

## Sources

- David R. Karger, "Minimum Cuts in Near-Linear Time", Journal of the ACM (2000), arXiv:cs/9812007.
- Crispin St. J. A. Nash-Williams, "Edge-Disjoint Spanning Trees of Finite Graphs", Journal of the London Mathematical Society (1961).
- William T. Tutte, "On the Problem of Decomposing a Graph into n Connected Factors", Journal of the London Mathematical Society (1961).
