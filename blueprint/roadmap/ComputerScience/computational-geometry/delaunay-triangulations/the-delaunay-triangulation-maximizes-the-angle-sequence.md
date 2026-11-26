# The Delaunay triangulation maximizes the angle sequence

Let $P$ be a set of $n \ge 3$ points in $\mathbb{R}^2$, not all on one line. A *triangulation* of $P$ is a maximal planar subdivision with vertex set $P$: a maximal set of closed segments with endpoints in $P$ that meet only in common endpoints and contain no other point of $P$; its bounded faces are triangles whose union is $\operatorname{conv}(P)$.

Assume no four points of $P$ lie on a common circle. Associate with each triangulation of $P$ the sequence of the angles of all its triangles sorted increasingly; all such sequences have the same length. Among all triangulations of $P$, the Delaunay triangulation has the lexicographically largest angle sequence; in particular it maximizes the smallest angle.

## Depends on

- [Delaunay triangulation](delaunay-triangulation.md)

## Proof depends on

- [Lawson's flip algorithm](lawson-s-flip-algorithm.md)
- [Existence and uniqueness of the Delaunay triangulation](existence-and-uniqueness-of-the-delaunay-triangulation.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 12, the theorem that among all triangulations of a planar point set the Delaunay triangulation has the lexicographically largest angle sequence
- *Geometric Algorithms*, course slides, Utrecht University, 2023, "Delaunay triangulations", <https://ics-websites.science.uu.nl/docs/vakken/ga/2023/slides/slides9.pdf>: the theorem that any angle-optimal triangulation is a Delaunay triangulation and any Delaunay triangulation maximizes the minimum angle
