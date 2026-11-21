# Graph minor theorem (Robertson–Seymour)

The finite graphs are well-quasi-ordered by the minor relation: every infinite sequence
$G_0, G_1, \dots$ of finite graphs has two terms $G_i, G_j$ with $i < j$ such that $G_i$ is a minor
of $G_j$. Equivalently, there is no infinite set of pairwise incomparable finite graphs.

Robertson and Seymour's proof spans their series *Graph Minors* (1983–2012). In the source's
sketch, one may assume that no later term has the first term $G_0$ as a minor. If $G_0$ is planar,
the later terms have bounded tree-width by the grid theorem and the bounded case applies. In
general one may take $G_0 = K_n$, and the proof uses the structure of graphs with no $K_n$ minor:
tree-decompositions into parts nearly embeddable in finitely many surfaces.

## Informally uses

- [Graphs of bounded tree-width are well-quasi-ordered by minors (Robertson–Seymour)](../tree-width/exists-is-minor-of-has-treewidth-at-most.md):
  the bounded case.
- [Grid theorem (Robertson–Seymour)](../tree-width/exists-grid-minor-of-not-has-treewidth-a.md):
  graphs with no $G_0$ minor, for planar $G_0$, have bounded tree-width (the source's
  Corollary 12.6.4).

## Background

- [Robertson–Seymour theorem](robertson-seymour.md): the forbidden-minor form.

## Sources

- Reinhard Diestel, *Graph Theory*, 6th edition, author's online preview of Chapter 12 (PDF dated 28 June 2024), https://www.math.uni-hamburg.de/home/diestel/books/graph.theory/preview/Ch12.pdf, Theorem 12.7.1 (with its proof sketch at the end of Section 12.7).
