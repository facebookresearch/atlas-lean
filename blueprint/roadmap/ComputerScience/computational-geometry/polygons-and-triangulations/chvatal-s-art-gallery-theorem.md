# Chvátal's art gallery theorem

A point $x$ of a simple polygon $P$ (a closed region) *sees* a point $y \in P$ if the closed segment $xy$ is contained in $P$. For a simple polygon $P$ let $G(P)$ be the least number of points of $P$ such that every point of $P$ is seen by one of them, and let $g(n)$ be the largest value of $G(P)$ over simple polygons with $n$ vertices. Then $g(n) = \lfloor n/3 \rfloor$ for every $n \ge 3$: $\lfloor n/3 \rfloor$ guards always suffice, and they can be placed at vertices of $P$, and for every $n \ge 3$ some polygon with $n$ vertices needs that many.

## Depends on

- [Simple polygons](simple-polygons.md)

## Proof depends on

- [Three-colorability of polygon triangulations](three-colorability-of-polygon-triangulations.md)
- [Triangulation theorem for simple polygons](triangulation-theorem-for-simple-polygons.md)

## Sources

- J. O'Rourke, *Art Gallery Theorems and Algorithms*, Oxford University Press, 1987, Chapter 1, <https://www.science.smith.edu/~jorourke/books/ArtGalleryTheorems/Art_Gallery_Chapter_1.pdf>: Section 1.2.1, the definitions of $G(P)$ and $g(n)$, Theorem 1.1 and Fisk's proof by 3-coloring a triangulation
- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 33, "The Art-Gallery Theorem" and the comb polygon that needs $n/3$ guards
- S. Fisk, "A short proof of Chvátal's watchman theorem", *Journal of Combinatorial Theory, Series B* 24(3):374, 1978
