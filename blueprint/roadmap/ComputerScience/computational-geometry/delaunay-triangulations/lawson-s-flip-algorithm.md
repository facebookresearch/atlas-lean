# Lawson's flip algorithm

Let $P$ be a set of $n \ge 3$ points in $\mathbb{R}^2$, not all on one line. A *triangulation* of $P$ is a maximal planar subdivision with vertex set $P$: a maximal set of closed segments with endpoints in $P$ that meet only in common endpoints and contain no other point of $P$; its bounded faces are triangles whose union is $\operatorname{conv}(P)$.

Assume no four points of $P$ lie on a common circle. Start from any triangulation of $P$ and, as long as some edge is illegal, flip one illegal edge. Each flip makes the sequence of the angles of all triangles, sorted increasingly, lexicographically larger; hence the process terminates after finitely many flips, and the triangulation it ends with is a Delaunay triangulation of $P$.

## Depends on

- [Delaunay triangulation](delaunay-triangulation.md)
- [The in-circle criterion for illegal edges](the-in-circle-criterion-for-illegal-edges.md)

## Proof depends on

- [Delaunay's theorem on locally Delaunay triangulations](delaunay-s-theorem-on-locally-delaunay-triangulations.md)
- [Number of triangles and edges of a triangulation](number-of-triangles-and-edges-of-a-triangulation.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 12, "Maximizing Angles and Edge Flipping": each flip increases the sorted angle sequence and the process terminates with the triangulation satisfying the empty circle condition
- *Geometric Algorithms*, course slides, Utrecht University, 2023, "Delaunay triangulations", <https://ics-websites.science.uu.nl/docs/vakken/ga/2023/slides/slides9.pdf>: the theorem that a triangulation is legal if and only if it is a Delaunay triangulation
