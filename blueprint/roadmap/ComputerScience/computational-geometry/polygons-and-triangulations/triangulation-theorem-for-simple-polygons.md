# Triangulation theorem for simple polygons

Every simple polygon $P$ with $n \ge 3$ vertices can be partitioned into $n - 2$ triangles by adding $n - 3$ diagonals. More precisely, every polygon with $n \ge 4$ vertices has a diagonal, which splits it into two simple polygons with $n_1$ and $n_2$ vertices where $n_1 + n_2 = n + 2$; by induction every triangulation of $P$ consists of exactly $n - 3$ diagonals and $n - 2$ triangles.

## Depends on

- [Diagonals and triangulations of a simple polygon](diagonals-and-triangulations-of-a-simple-polygon.md)

## Sources

- J. O'Rourke, *Art Gallery Theorems and Algorithms*, Oxford University Press, 1987, Chapter 1, <https://www.science.smith.edu/~jorourke/books/ArtGalleryTheorems/Art_Gallery_Chapter_1.pdf>: Theorem 1.2 (Triangulation Theorem) and its proof, which finds a diagonal at a convex vertex
- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 33, the lemma that every simple polygon with $n$ vertices has a triangulation with $n - 3$ diagonals and $n - 2$ triangles
