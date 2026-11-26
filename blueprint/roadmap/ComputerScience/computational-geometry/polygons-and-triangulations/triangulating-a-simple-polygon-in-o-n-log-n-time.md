# Triangulating a simple polygon in $O(n \log n)$ time

Every simple polygon with $n$ vertices can be triangulated in $O(n \log n)$ time, by partitioning it into monotone pieces and triangulating each piece in time linear in its size.

## Depends on

- [Diagonals and triangulations of a simple polygon](diagonals-and-triangulations-of-a-simple-polygon.md)

## Proof depends on

- [Partition of a simple polygon into monotone pieces](partition-of-a-simple-polygon-into-monotone-pieces.md)
- [Triangulating a monotone polygon in linear time](triangulating-a-monotone-polygon-in-linear-time.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 5, the theorem that a simple polygon with $n$ vertices can be triangulated in $O(n \log n)$ time
- *Geometric Algorithms*, course slides, Utrecht University, 2023, "Triangulating a polygon", <https://ics-websites.science.uu.nl/docs/vakken/ga/2023/slides/slides3.pdf>: the theorem that a simple polygon with $n$ vertices can be triangulated in $O(n \log n)$ time
