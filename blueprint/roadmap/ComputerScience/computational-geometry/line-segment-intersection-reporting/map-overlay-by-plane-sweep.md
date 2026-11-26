# Map overlay by plane sweep

Let $S_1$ and $S_2$ be planar subdivisions, each given as a doubly-connected edge list, of total complexity $n$ (vertices, edges and faces), and let $k$ be the number of vertices of their overlay, the subdivision induced by the union of their edges. Then a doubly-connected edge list of the overlay, with each of its faces labelled by the faces of $S_1$ and $S_2$ that contain it, can be computed in $O(n \log n + k \log n)$ time, by the plane sweep for segment intersection over the edges of both subdivisions.

## Depends on

- [Doubly-connected edge list](doubly-connected-edge-list.md)

## Proof depends on

- [Bentley–Ottmann plane sweep](bentley-ottmann-plane-sweep.md)

## Sources

- *Geometric Algorithms*, course slides, Utrecht University, 2023, "Subdivision representation and map overlay", <https://ics-websites.science.uu.nl/docs/vakken/ga/2023/slides/slides2b.pdf>: the theorem that the overlay of two planar subdivisions can be computed in $O(n \log n + k \log n)$ time, where $k$ is the number of vertices of the overlay
- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 10, "Merging subdivisions"
