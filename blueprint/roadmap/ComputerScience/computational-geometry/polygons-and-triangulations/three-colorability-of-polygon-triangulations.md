# Three-colorability of polygon triangulations

Let $\mathcal{T}$ be a triangulation of a simple polygon and let $G$ be the graph whose vertices are the polygon's vertices and whose edges are the polygon's edges and the diagonals of $\mathcal{T}$. Then $G$ has a proper vertex coloring with three colors, and in every proper $3$-coloring the three vertices of each triangle of $\mathcal{T}$ receive three different colors. The proof is by induction on the number of triangles: a leaf of the dual tree of $\mathcal{T}$ is a triangle of $\mathcal{T}$ with two polygon edges; removing it leaves a triangulated polygon, colored by induction, and the removed vertex gets the color not used on the diagonal.

## Depends on

- [Diagonals and triangulations of a simple polygon](diagonals-and-triangulations-of-a-simple-polygon.md)

## Proof depends on

- [The dual of a polygon triangulation is a tree](the-dual-of-a-polygon-triangulation-is-a-tree.md)

## Sources

- J. O'Rourke, *Art Gallery Theorems and Algorithms*, Oxford University Press, 1987, Chapter 1, <https://www.science.smith.edu/~jorourke/books/ArtGalleryTheorems/Art_Gallery_Chapter_1.pdf>: Section 1.3.1, the induction after Theorem 1.3 that cuts off an ear to 3-color a polygon triangulation
- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 33, the lemma that the triangulation graph of a simple polygon is 3-colorable, proved by removing a leaf of the dual tree
