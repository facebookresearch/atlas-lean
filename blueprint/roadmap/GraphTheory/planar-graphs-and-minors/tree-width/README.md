# Tree-width

A tree-decomposition of a graph arranges its vertices in bags indexed by the nodes of a tree, so
that the bags cover every vertex and every edge and the bags containing any fixed vertex form a
subtree. Its width is the largest bag size minus one, and the tree-width of the graph is the least
width of a tree-decomposition: trees with an edge have tree-width one and the complete graph $K_n$
has tree-width $n - 1$. Tree-width does not increase under taking minors, it is characterised
exactly by brambles (Seymour–Thomas), large tree-width forces a large grid minor
(Robertson–Seymour), and graphs of bounded tree-width are well-quasi-ordered by minors, the first
step towards the [graph minor theorem](../graph-minors/graph-minor-theorem.md). Pages follow
R. Diestel, *Graph Theory*, 6th edition, Sections 12.3, 12.4 and 12.6 (author's online preview of
Chapter 12, PDF dated 28 June 2024).

Tree-width is recorded as the predicate "tree-width at most $k$" for natural numbers $k$, so the
convention that the graph with no vertices has tree-width $-1$ is never needed: that graph has
tree-width at most every $k$.

- [Tree-decomposition](tree-decomposition.md)
- [Width at most $k$](has-width-at-most.md)
- [Tree-width at most $k$](has-treewidth-at-most.md)
- [Tree-width bounds are monotone](mono.md)
- [The one-bag decomposition](has-treewidth-at-most-of-encard-le.md)
- [A graph with an edge has tree-width at least one](not-has-treewidth-at-most-zero-of-adj.md)
- [Every clique lies in a bag](exists-bag-superset.md)
- [Tree-width of complete graphs](has-treewidth-at-most-top-iff.md)
- [Trees have tree-width at most one](has-treewidth-at-most-one.md)
- [Tree-width does not increase under taking minors](has-treewidth-at-most-2.md)
- [Touching vertex sets](touch.md)
- [Touching is symmetric](symm.md)
- [Bramble](is-bramble.md)
- [Bramble of order greater than $k$](order-gt.md)
- [Small graphs have no large brambles](not-order-gt-of-card-le.md)
- [Tree-width duality theorem (Seymour–Thomas)](has-treewidth-at-most-iff-forall-bramble.md)
- [Grid theorem (Robertson–Seymour)](exists-grid-minor-of-not-has-treewidth-a.md)
- [Graphs of bounded tree-width are well-quasi-ordered by minors (Robertson–Seymour)](exists-is-minor-of-has-treewidth-at-most.md)

## Related topics

- [Rank-width and vertex-minors](../rank-width-and-vertex-minors/README.md): the analogous width
  parameter for dense graphs; rank-width is at most tree-width plus one.
- [Graph minors](../graph-minors/README.md): the minor relation under which tree-width is
  monotone and the graph minor theorem.
