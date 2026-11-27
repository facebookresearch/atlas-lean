# The Delaunay triangulation is a geometric spanner

Let $P$ be a set of $n \ge 3$ points in $\mathbb{R}^2$, not all on one line. A *triangulation* of $P$ is a maximal planar subdivision with vertex set $P$: a maximal set of closed segments with endpoints in $P$ that meet only in common endpoints and contain no other point of $P$; its bounded faces are triangles whose union is $\operatorname{conv}(P)$.

Assume no four points of $P$ lie on a common circle and let $t = 4\pi\sqrt{3}/9 \approx 2.418$. For all $p, q \in P$, the shortest path from $p$ to $q$ in the Delaunay triangulation of $P$, with edges weighted by their Euclidean length, has length at most $t \, \|p - q\|$.

## Depends on

- [Delaunay triangulation](delaunay-triangulation.md)
- [Existence and uniqueness of the Delaunay triangulation](existence-and-uniqueness-of-the-delaunay-triangulation.md)

## Expansion

This page becomes ready once:

- Source check: the proof is in J. M. Keil and C. A. Gutwin, "Classes of graphs which approximate the complete Euclidean graph" (1992), which has not been opened; the lecture notes state the result without proof. Its Section 2, Lemma 1 (the upper-arc prerequisite) and Theorem 1 (the stretch constant) are the locators to check.

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 12, "Spanner Properties": the theorem, due to Keil and Gutwin, that the Delaunay triangulation is a $t$-spanner for $t = 4\pi\sqrt{3}/9$
