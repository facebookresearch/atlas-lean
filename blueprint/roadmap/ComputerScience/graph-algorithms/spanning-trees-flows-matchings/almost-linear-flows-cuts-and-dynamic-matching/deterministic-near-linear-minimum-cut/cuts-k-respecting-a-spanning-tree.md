# Cuts that k-respect a spanning tree

Let $G = (V, E, w)$ be a connected undirected graph and $T$ a spanning tree of $G$. For an integer $k \ge 1$, a cut $S$ (with $\emptyset \ne S \subsetneq V$) *$k$-respects* $T$ if $|\partial S \cap E(T)| \le k$, and it is *determined* by the tree edges $\partial S \cap E(T)$. Every cut crosses at least one tree edge. If $F \subseteq E(T)$ with $|F| \in \{1, 2\}$, there is exactly one cut, up to complementation, with $\partial S \cap E(T) = F$: for $F = \{e\}$ it is a component of $T - e$, and for $F = \{e, f\}$ it is the middle component of $T - \{e, f\}$. The *minimum $2$-respecting cut problem* asks for $\min \{ w(\partial S) : S \text{ 2-respects } T \}$.

## Depends on

- [Spanning tree](../../../../../GraphTheory/algebraic-graph-theory/part-01/kirchhoff-s-matrix-tree-theorem/is-spanning-tree.md)
- [Cuts of a multigraph](../../../../randomized-algorithms/karger-s-algorithm/is-cut.md)

## Sources

- David R. Karger, "Minimum Cuts in Near-Linear Time", Journal of the ACM (2000), arXiv:cs/9812007.
- Pawel Gawrychowski, Shay Mozes, Oren Weimann, "Minimum Cut in O(m log^2 n) Time", ICALP (2020), arXiv:1911.01145.
