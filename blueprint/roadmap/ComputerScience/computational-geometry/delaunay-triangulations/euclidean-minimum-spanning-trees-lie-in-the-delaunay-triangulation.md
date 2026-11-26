# Euclidean minimum spanning trees lie in the Delaunay triangulation

Let $P$ be a set of $n \ge 3$ points in $\mathbb{R}^2$, not all on one line. A *triangulation* of $P$ is a maximal planar subdivision with vertex set $P$: a maximal set of closed segments with endpoints in $P$ that meet only in common endpoints and contain no other point of $P$; its bounded faces are triangles whose union is $\operatorname{conv}(P)$.

Assume no four points of $P$ lie on a common circle. Let $T$ be a minimum spanning tree of the complete graph on $P$ in which the edge $pq$ has weight $\|p - q\|$. Then every edge of $T$ is an edge of the Delaunay triangulation of $P$.

## Depends on

- [Delaunay triangulation](delaunay-triangulation.md)

## Proof depends on

- [Empty circle characterization of Delaunay edges](empty-circle-characterization-of-delaunay-edges.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 12, "Euclidean Minimum Spanning Tree": the theorem that the minimum spanning tree is a subgraph of the Delaunay triangulation
- *Geometric Algorithms*, course slides, Utrecht University, 2023, "Delaunay triangulations", <https://ics-websites.science.uu.nl/docs/vakken/ga/2023/slides/slides9.pdf>: the lemma that every edge of the Euclidean minimum spanning tree is an edge of the Delaunay graph
