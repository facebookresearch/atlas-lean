# Triangulating a simple polygon in $O(n \log n)$ time

Every simple polygon with $n$ vertices can be triangulated in $O(n \log n)$ time, by partitioning it into monotone pieces and triangulating each piece in time linear in its size. Both steps assume that no two vertices have the same $x$-coordinate. A general polygon is first sheared by $(x, y) \mapsto (x + \varepsilon y, y)$ with $0 < \varepsilon < g/H$, where $g$ is the least positive difference between two vertex $x$-coordinates and $H$ the difference between the largest and smallest vertex $y$-coordinates, both found in $O(n \log n)$ time by sorting. Afterwards no two vertices share an $x$-coordinate, and since the shear is an affine bijection it maps the polygon, its diagonals and its triangulations to those of the sheared polygon.

## Depends on

- [Diagonals and triangulations of a simple polygon](diagonals-and-triangulations-of-a-simple-polygon.md)

## Proof depends on

- [Partition of a simple polygon into monotone pieces](partition-of-a-simple-polygon-into-monotone-pieces.md)
- [Triangulating a monotone polygon in linear time](triangulating-a-monotone-polygon-in-linear-time.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 5, the theorem that a simple polygon with $n$ vertices can be triangulated in $O(n \log n)$ time
- *Geometric Algorithms*, course slides, Utrecht University, 2023, "Triangulating a polygon", <https://ics-websites.science.uu.nl/docs/vakken/ga/2023/slides/slides3.pdf>: the theorem that a simple polygon with $n$ vertices can be triangulated in $O(n \log n)$ time
