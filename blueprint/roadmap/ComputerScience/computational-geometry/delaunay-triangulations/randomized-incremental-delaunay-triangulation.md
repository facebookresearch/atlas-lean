# Randomized incremental Delaunay triangulation

Let $P$ be a set of $n \ge 3$ points in $\mathbb{R}^2$, not all on one line. A *triangulation* of $P$ is a maximal planar subdivision with vertex set $P$: a maximal set of closed segments with endpoints in $P$ that meet only in common endpoints and contain no other point of $P$; its bounded faces are triangles whose union is $\operatorname{conv}(P)$.

Assume no four points of $P$ lie on a common circle and no three on a common line. The randomized incremental algorithm starts from three sentinel points forming a triangle that contains $P$, chosen so far out that they lie in no circumcircle of a triangle of the final triangulation and so that no three of the $n + 3$ points lie on a common line (so that a new point never lies on an edge of the current triangulation); it inserts the points of $P$ in an order chosen uniformly at random, locates each new point in the triangle of the current Delaunay triangulation that contains it, joins it to the vertices of that triangle and restores the Delaunay property by flipping edges that fail the in-circle test, keeping every uninserted point in a bucket of the triangle that contains it, and at the end removes the sentinels and their incident triangles. It computes the Delaunay triangulation of $P$; the expected number of edge changes per insertion is $O(1)$, and the expected total running time is $O(n \log n)$, the expectation being over the insertion order only.

## Depends on

- [Delaunay triangulation](delaunay-triangulation.md)
- [Average formula for the expected time over random orderings](../../randomized-algorithms/average-case-running-time/expected-time-uniform-permutation.md)

## Proof depends on

- [Delaunay's theorem on locally Delaunay triangulations](delaunay-s-theorem-on-locally-delaunay-triangulations.md)
- [Number of triangles and edges of a triangulation](number-of-triangles-and-edges-of-a-triangulation.md)
- [The in-circle test as a lifted orientation test](the-in-circle-test-as-a-lifted-orientation-test.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 13, "Constructing the Delaunay Triangulation", the incremental update with three sentinel points and its footnote on choosing them (the update joins the new point to the three vertices of the triangle containing it, which presumes general position), and "Running-Time Analysis": $O(1)$ expected structural changes per insertion and $O(n \log n)$ expected time
