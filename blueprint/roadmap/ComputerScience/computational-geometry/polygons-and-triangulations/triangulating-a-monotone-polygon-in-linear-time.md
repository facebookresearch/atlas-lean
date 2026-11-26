# Triangulating a monotone polygon in linear time

Let $P$ be a simple polygon with $n$ vertices that is monotone with respect to the $x$-axis, with no two vertices of the same $x$-coordinate, given as its cyclic vertex list. Merging its upper and lower chains by $x$-coordinate and sweeping from left to right while maintaining the untriangulated region to the left of the current vertex (two $x$-monotone chains, one of them a reflex chain) as a stack, one obtains a triangulation of $P$ in $O(n)$ time.

## Depends on

- [Diagonals and triangulations of a simple polygon](diagonals-and-triangulations-of-a-simple-polygon.md)
- [Monotone polygons](monotone-polygons.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 5, "Triangulation of Monotone Polygons" and its main invariant
- *Geometric Algorithms*, course slides, Utrecht University, 2023, "Triangulating a polygon", <https://ics-websites.science.uu.nl/docs/vakken/ga/2023/slides/slides3.pdf>: the theorem that a monotone polygon with $n$ vertices can be triangulated in $O(n)$ time
