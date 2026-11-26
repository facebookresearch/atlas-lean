# Delaunay's theorem on locally Delaunay triangulations

Let $P$ be a set of $n \ge 3$ points in $\mathbb{R}^2$, not all on one line. A *triangulation* of $P$ is a maximal planar subdivision with vertex set $P$: a maximal set of closed segments with endpoints in $P$ that meet only in common endpoints and contain no other point of $P$; its bounded faces are triangles whose union is $\operatorname{conv}(P)$.

Assume no four points of $P$ lie on a common circle. An edge $ab$ of a triangulation $T$ of $P$ shared by the triangles $abc$ and $abd$ is *locally Delaunay* if $d$ does not lie in the interior of the circumcircle of $abc$; edges on the boundary of $\operatorname{conv}(P)$ count as locally Delaunay. Then $T$ is a Delaunay triangulation if and only if all its edges are locally Delaunay.

## Depends on

- [Delaunay triangulation](delaunay-triangulation.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 13, "Delaunay's Theorem: A triangulation is globally Delaunay iff it is locally Delaunay"
