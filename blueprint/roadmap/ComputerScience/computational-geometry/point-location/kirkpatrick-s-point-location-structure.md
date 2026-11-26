# Kirkpatrick's point location structure

Let $T_0$ be a triangulation of the plane by a planar straight-line graph with $n$ vertices whose outer face is the exterior of a triangle $abc$. Repeatedly delete from $T_i$ an independent set of vertices of degree at most $8$, not containing $a$, $b$ or $c$, and retriangulate the holes to obtain $T_{i+1}$, until only the triangle $abc$ remains; link each triangle of $T_{i+1}$ to the at most $8$ triangles of $T_i$ that it overlaps. The resulting hierarchy has $O(\log n)$ levels and size $O(n)$, and the triangle of $T_0$ containing a query point is found in $O(\log n)$ time by descending from $abc$ through the levels.

## Depends on

- [Straight-line planar graph](../../../GraphTheory/planar-graphs-and-minors/straight-line-planar-drawings/is-planar.md)

## Proof depends on

- [Low-degree independent sets in maximal planar graphs](low-degree-independent-sets-in-maximal-planar-graphs.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 22, "Kirkpatrick's Algorithm" and "Construction and Analysis": $O(\log n)$ levels, size at most $18n$ and $O(\log n)$ query time
