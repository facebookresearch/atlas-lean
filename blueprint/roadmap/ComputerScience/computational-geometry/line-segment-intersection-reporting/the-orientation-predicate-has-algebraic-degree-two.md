# The orientation predicate has algebraic degree two

The *algebraic degree* of a geometric predicate, for a fixed representation of its inputs by real coordinates, is the least degree of a polynomial in the input coordinates whose sign decides the predicate. For points $p, q, r \in \mathbb{R}^2$ in Cartesian coordinates, the orientation predicate (is $r$ strictly to the right of the oriented line through $p$ and $q$?) has algebraic degree two: it is decided by the sign of the determinant $(q_x - p_x)(r_y - p_y) - (q_y - p_y)(r_x - p_x)$, which is negative exactly when $r$ is strictly to the right and is the negative of the direction of $p, q, r$, and no polynomial of degree at most one decides it.

## Depends on

- [Direction of three points](../orientation-and-segment-intersection-tests/direction.md)

## Sources

- *Computational Geometry*, lecture notes, ETH Zürich, autumn 2013, Chapter 5 (Line sweep), <https://ti.inf.ethz.ch/ew/courses/CG13/lecture/Chapter%205.pdf>: Section 5.4, the definition of the algebraic degree of a predicate, Proposition 5.13 and Exercise 5.14 (no polynomial of degree at most one describes the orientation test)
