# Partition of a simple polygon into monotone pieces

Let $P$ be a simple polygon with $n$ vertices, no two of them with the same $x$-coordinate. A plane sweep from left to right, which keeps the polygon edges crossing the sweep line in a balanced search tree together with a *helper* vertex for each edge and adds a diagonal at every split vertex and merge vertex (reflex vertices whose two incident edges both lie to their right, respectively to their left), adds non-crossing diagonals of $P$ that partition it into polygons monotone with respect to the $x$-axis, in $O(n \log n)$ time. Its correctness uses the characterization of monotone polygons by interior cusps with the roles of $x$ and $y$ exchanged: the added diagonals remove every split and merge vertex, the interior cusps for the $x$-direction.

## Depends on

- [Diagonals and triangulations of a simple polygon](diagonals-and-triangulations-of-a-simple-polygon.md)
- [Monotone polygons](monotone-polygons.md)

## Proof depends on

- [Polygons without interior cusps are monotone](polygons-without-interior-cusps-are-monotone.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 5, "Monotone Subdivision": split and merge vertices, helpers, and the theorem that the sweep decomposes an $n$-vertex simple polygon into monotone pieces in $O(n \log n)$ time
- *Geometric Algorithms*, course slides, Utrecht University, 2023, "Triangulating a polygon", <https://ics-websites.science.uu.nl/docs/vakken/ga/2023/slides/slides3.pdf>: the theorem that a simple polygon with $n$ vertices can be partitioned into monotone pieces in $O(n \log n)$ time
