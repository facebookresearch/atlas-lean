# Tree-width at most $k$

A graph $G$ has tree-width at most $k$, for a natural number $k$, if it has a tree-decomposition
all of whose bags have at most $k + 1$ vertices. The tree-width $\mathrm{tw}(G)$ is the least
width of a tree-decomposition, so for a finite graph and $k \ge 0$ this is
$\mathrm{tw}(G) \le k$. For a graph with infinitely many vertices the predicate is always false,
because the decomposition tree is finite and so are the bags; it is meant for finite graphs only.

The graph with no vertices has tree-width $-1$ under the usual definition (a single empty bag has
width $-1$); it satisfies this predicate for every natural number $k$, which is consistent with
that convention, and the value $-1$ itself is not represented.

## Sources

- Reinhard Diestel, *Graph Theory*, 6th edition, author's online preview of Chapter 12 (PDF dated 28 June 2024), https://www.math.uni-hamburg.de/home/diestel/books/graph.theory/preview/Ch12.pdf, Section 12.4.
