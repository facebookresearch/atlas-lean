# Tree-width of complete graphs

Let $V$ be a finite set with $n$ elements. The complete graph on $V$ has tree-width at most $k$
if and only if $n \le k + 1$. Hence $\mathrm{tw}(K_n) = n - 1$ for every $n \ge 1$; for $n = 0$ the
statement says that the graph with no vertices has tree-width at most every $k$.

The upper bound puts all vertices in a single bag. The lower bound is the case $K = V$ of the
fact that every clique lies in a bag.

## Background

- [Complete graphs have cut-rank at most one](../rank-width-and-vertex-minors/cut-rank-top-le-one.md):
  in contrast, complete graphs have rank-width at most one, so tree-width is not bounded by any
  function of rank-width.

## Sources

- Reinhard Diestel, *Graph Theory*, 6th edition, author's online preview of Chapter 12 (PDF dated 28 June 2024), https://www.math.uni-hamburg.de/home/diestel/books/graph.theory/preview/Ch12.pdf, Section 12.4 and Corollary 12.3.5.
