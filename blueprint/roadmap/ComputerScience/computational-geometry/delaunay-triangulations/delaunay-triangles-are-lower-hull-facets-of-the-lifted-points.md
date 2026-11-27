# Delaunay triangles are the lower faces of the lifted points

Let $P$ be a set of $n \ge 3$ points in $\mathbb{R}^2$, not all on one line. A *triangulation* of $P$ is a maximal planar subdivision with vertex set $P$: a maximal set of closed segments with endpoints in $P$ that meet only in common endpoints and contain no other point of $P$; its bounded faces are triangles whose union is $\operatorname{conv}(P)$.

Assume no four points of $P$ lie on a common circle and let $P^\uparrow = \{(x, y, x^2 + y^2) : (x, y) \in P\}$. For distinct $p, q, r \in P$, not on a common line, the triangle $pqr$ is a triangle of the Delaunay triangulation of $P$ if and only if every point of $P^\uparrow \setminus \{p^\uparrow, q^\uparrow, r^\uparrow\}$ lies strictly above the plane through $p^\uparrow$, $q^\uparrow$ and $r^\uparrow$; that is, if and only if $p^\uparrow q^\uparrow r^\uparrow$ is a two-dimensional face of the lower convex hull of $P^\uparrow$, exposed by a non-vertical plane with all of $P^\uparrow$ on or above it. For $n \ge 4$ points, not all on a line, the set $P^\uparrow$ spans $\mathbb{R}^3$ (four coplanar lifted points would be cocircular or collinear), so these faces are facets of $\operatorname{conv}(P^\uparrow)$ with downward outer normal; for $n = 3$ the face is the whole hull.

## Depends on

- [Delaunay triangulation](delaunay-triangulation.md)

## Proof depends on

- [The in-circle test as a lifted orientation test](the-in-circle-test-as-a-lifted-orientation-test.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 35, the theorem that $\triangle pqr$ is a Delaunay triangle if and only if $\triangle p^\uparrow q^\uparrow r^\uparrow$ is a face of the lower convex hull of $P^\uparrow$ (a face, not necessarily a facet)
