# Trees have tree-width at most one

Every finite tree has tree-width at most one. Root the tree $G$ at a vertex $r$; give each vertex
$v$ the bag consisting of $v$ and its parent, the unique neighbour of $v$ closer to $r$ (the root
has the bag $\{r\}$). With $G$ itself as decomposition tree these bags satisfy (T1)–(T3) and
have at most two vertices.

A tree with at least one edge has tree-width exactly one, since a graph with an edge has
tree-width at least one.

## Background

- [A graph with an edge has tree-width at least one](not-has-treewidth-at-most-zero-of-adj.md):
  the matching lower bound for trees with an edge.

## Sources

- Reinhard Diestel, *Graph Theory*, 6th edition, author's online preview of Chapter 12 (PDF dated 28 June 2024), https://www.math.uni-hamburg.de/home/diestel/books/graph.theory/preview/Ch12.pdf, Section 12.4 ("As one easily checks, trees themselves have tree-width 1").
