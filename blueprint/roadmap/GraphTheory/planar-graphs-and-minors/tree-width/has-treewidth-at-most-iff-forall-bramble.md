# Tree-width duality theorem (Seymour–Thomas)

Let $G$ be a finite graph and $k$ a natural number. Then $G$ has tree-width at most $k$ if and only
if $G$ contains no bramble of order greater than $k + 1$.

The source states: for every integer $k \ge 0$, a graph has tree-width $< k$ if and only if it
contains no bramble of order $> k$. The statement here is the case $k + 1$ of it, for
$k + 1 \ge 1$; the source's case $k = 0$ concerns only the graph with no vertices and is not
included. For example, the crosses of the $k \times k$ grid form a bramble of order $k$, so the grid
has tree-width at least $k - 1$.

## Background

- [Tree-decomposition](tree-decomposition.md) and [bramble](is-bramble.md): the two sides of the
  duality.
- [Every clique lies in a bag](exists-bag-superset.md): the forward direction of the source's
  proof shows, in the same way, that some bag covers any given bramble.

## Sources

- Reinhard Diestel, *Graph Theory*, 6th edition, author's online preview of Chapter 12 (PDF dated 28 June 2024), https://www.math.uni-hamburg.de/home/diestel/books/graph.theory/preview/Ch12.pdf, Theorem 12.4.3.
- P. D. Seymour and R. Thomas, *Graph searching and a min-max theorem for tree-width*, J. Combin.
  Theory Ser. B 58 (1993) 22–33 (the original; not consulted here).
