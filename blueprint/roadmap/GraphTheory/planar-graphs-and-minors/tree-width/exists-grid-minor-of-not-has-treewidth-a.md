# Grid theorem (Robertson–Seymour)

For every natural number $r$ there is a natural number $k$ such that every finite graph whose
tree-width is greater than $k$ has the $r \times r$ grid as a minor. The grid is the box product of
two paths on $r$ vertices: its vertices are the pairs $(i, j)$ with $0 \le i, j < r$, and two pairs
are adjacent when they differ by one in exactly one coordinate.

The source states the theorem for graphs of tree-width at least $k$; since $k$ is existentially
quantified, "greater than $k$" is the same statement.

## Background

- [Tree-width duality theorem (Seymour–Thomas)](has-treewidth-at-most-iff-forall-bramble.md):
  grids have large tree-width because their crosses form a bramble of large order.
- [Graph minor theorem](../graph-minors/graph-minor-theorem.md): the source uses the grid
  theorem in its proof.

## Sources

- Reinhard Diestel, *Graph Theory*, 6th edition, author's online preview of Chapter 12 (PDF dated 28 June 2024), https://www.math.uni-hamburg.de/home/diestel/books/graph.theory/preview/Ch12.pdf, Theorem 12.6.3.
- N. Robertson and P. D. Seymour, *Graph minors. V. Excluding a planar graph*, J. Combin. Theory
  Ser. B (1986) (the original, the source of Diestel's Theorem 12.6.3; not consulted here).
