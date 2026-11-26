# Map overlay by plane sweep

Let $S_1$ and $S_2$ be planar subdivisions, each given as a doubly-connected edge list, of total complexity $n$ (vertices, edges and faces), and let $k$ be the number of vertices of their overlay, the subdivision induced by the union of their edges. Vertices may have any degree, edges of $S_1$ may cross or touch edges of $S_2$ and pass through their vertices, and faces may have holes; assume that no edge of $S_1$ overlaps an edge of $S_2$ in a segment of positive length. Then a doubly-connected edge list of the overlay, with each of its faces labelled by the faces of $S_1$ and $S_2$ that contain it, can be computed in $O(n \log n + k \log n)$ time. A plane sweep over the edges of both subdivisions handles, at each event point, all edges that end at it or pass through it (a vertex of $S_1$ or $S_2$, two coinciding vertices, an edge through a vertex of the other subdivision, or a crossing), in $O(\log n)$ time plus time proportional to the degrees involved; afterwards the boundary cycles of the faces are classified as outer or inner, and each inner cycle is attached to its face through the edge immediately to the left of its leftmost vertex.

## Depends on

- [Doubly-connected edge list](doubly-connected-edge-list.md)

## Informally uses

- [Bentley–Ottmann plane sweep](bentley-ottmann-plane-sweep.md)

## Sources

- *Geometric Algorithms*, course slides, Utrecht University, 2023, "Subdivision representation and map overlay", <https://ics-websites.science.uu.nl/docs/vakken/ga/2023/slides/slides2b.pdf>: slides 34–41 (the six types of overlay events), 45–49 (outer and inner boundary cycles and their faces) and 50 (the theorem that the overlay of two planar subdivisions can be computed in $O(n \log n + k \log n)$ time, where $k$ is the number of vertices of the overlay)
- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 10, "Merging subdivisions"
