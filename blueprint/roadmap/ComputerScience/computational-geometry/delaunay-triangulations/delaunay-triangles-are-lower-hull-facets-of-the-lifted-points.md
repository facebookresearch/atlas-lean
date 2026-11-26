# Delaunay triangles are lower hull facets of the lifted points

Let $P$ be a set of $n \ge 3$ points in $\mathbb{R}^2$, not all on one line. A *triangulation* of $P$ is a maximal planar subdivision with vertex set $P$: a maximal set of closed segments with endpoints in $P$ that meet only in common endpoints and contain no other point of $P$; its bounded faces are triangles whose union is $\operatorname{conv}(P)$.

Assume no four points of $P$ lie on a common circle and let $P^\uparrow = \{(x, y, x^2 + y^2) : (x, y) \in P\}$. For $p, q, r \in P$, the triangle $pqr$ is a triangle of the Delaunay triangulation of $P$ if and only if the triangle $p^\uparrow q^\uparrow r^\uparrow$ is a facet of the lower convex hull of $P^\uparrow$ (a facet of $\operatorname{conv}(P^\uparrow)$ whose outer normal points downward).

## Depends on

- [Delaunay triangulation](delaunay-triangulation.md)

## Proof depends on

- [The in-circle test as a lifted orientation test](the-in-circle-test-as-a-lifted-orientation-test.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 35, the theorem that $\triangle pqr$ is a Delaunay triangle if and only if $\triangle p^\uparrow q^\uparrow r^\uparrow$ is a face of the lower convex hull of $P^\uparrow$
