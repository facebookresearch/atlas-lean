# Tangents from an external point to a convex polygon

Let $K$ be a convex polygon in $\mathbb{R}^2$ with $m$ vertices, stored as an array in cyclic order, and let $p$ be a point outside $K$. Each of the two lines through $p$ that support $K$ (pass through a vertex of $K$ with $K$ on one side) can be computed with $O(\log m)$ orientation tests, by a variant of binary search over the vertex array.

## Depends on

- [Direction of three points](../orientation-and-segment-intersection-tests/direction.md)

## Sources

- T. M. Chan, "Optimal output-sensitive convex hull algorithms in two and three dimensions", *Discrete & Computational Geometry* 16 (1996), 361–368, <https://doi.org/10.1007/BF02712873>: Section 2, "tangent finding takes logarithmic time for a convex polygon by binary or Fibonacci search", used in each wrapping step
- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 3, the lemma on the two supporting lines of a convex polygon through an external point, used by Chan's algorithm
