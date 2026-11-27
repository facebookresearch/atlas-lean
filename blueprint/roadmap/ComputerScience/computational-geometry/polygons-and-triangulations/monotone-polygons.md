# Monotone polygons

A polygonal chain $p_1, \dots, p_k$ is *monotone with respect to a line* $L$ if the orthogonal projections of $p_1, \dots, p_k$ onto $L$ occur in the same order along $L$ as in the chain (consecutive vertices may project to the same point). A simple polygon is *monotone with respect to* $L$ if its boundary can be split into two chains that are both monotone with respect to $L$; it is *$y$-monotone* when $L$ is the $y$-axis. An *interior cusp* of a simple polygon is a reflex vertex (interior angle greater than $\pi$) such that neither of its two neighbouring vertices has larger $y$-coordinate than it, or neither has smaller $y$-coordinate than it (neighbours at the same height count on either side).

## Depends on

- [Simple polygons](simple-polygons.md)

## Sources

- J. O'Rourke, *Art Gallery Theorems and Algorithms*, Oxford University Press, 1987, Chapter 1, <https://www.science.smith.edu/~jorourke/books/ArtGalleryTheorems/Art_Gallery_Chapter_1.pdf>: Section 1.3.2, "Monotone Polygons": monotone chains and polygons and interior cusps
- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 5, "Monotone Polygons"
