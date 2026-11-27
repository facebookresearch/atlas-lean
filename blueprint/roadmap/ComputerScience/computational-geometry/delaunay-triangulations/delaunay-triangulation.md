# Delaunay triangulation

Let $P$ be a set of $n \ge 3$ points in $\mathbb{R}^2$, not all on one line. A *triangulation* of $P$ is a maximal planar subdivision with vertex set $P$: a maximal set of closed segments with endpoints in $P$ that meet only in common endpoints and contain no other point of $P$; its bounded faces are triangles whose union is $\operatorname{conv}(P)$.

A triangulation $T$ of $P$ is a *Delaunay triangulation* if for every triangle of $T$ no point of $P$ lies in the interior of the circle through its three vertices (its *circumcircle*).

## Depends on

- [Convex hull of a finite planar point set](../convex-hull-algorithms/convex-hull-of-a-finite-planar-point-set.md)

## Sources

- *Geometric Algorithms*, course slides, Utrecht University, 2023, "Delaunay triangulations", <https://ics-websites.science.uu.nl/docs/vakken/ga/2023/slides/slides9.pdf>: slide 22, the empty circle property characterizing Delaunay triangulations
- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 12, the circumcircle property
