# Every simple polygon with at least four vertices has a diagonal

Every simple polygon with $n \ge 4$ vertices has an interior diagonal, a segment between two non-adjacent vertices whose relative interior lies in the interior of the polygon (Dehn, Lennes).

In the proof, after a rotation that gives the vertices distinct $x$-coordinates, vertical cuts through the vertices decompose the closed polygon into trapezoids, each with exactly two vertices of the polygon on its boundary. If the segment between them crosses the interior of some trapezoid it is a diagonal. Otherwise every trapezoid has both vertices on its ceiling or both on its floor, and the polygon is a monotone mountain, which has a diagonal at a convex vertex.

## Depends on

- [Diagonals and triangulations of a simple polygon](diagonals-and-triangulations-of-a-simple-polygon.md)

## Proof depends on

- [A convex vertex of a monotone mountain cuts off an ear](a-convex-vertex-of-a-monotone-mountain-cuts-off-an-ear.md)
- [Jordan curve theorem for polygons](jordan-curve-theorem-for-polygons.md)

## Sources

- J. Erickson, *Computational Topology*, lecture notes, University of Illinois, 2023, Chapter 1 (Simple polygons), <https://jeffe.cs.illinois.edu/teaching/comptop/2023/notes/01-simple-polygons.pdf>: Section 1.4, the Diagonal Lemma (Dehn, Lennes) and its proof by the trapezoidal decomposition
- J. O'Rourke, *Art Gallery Theorems and Algorithms*, Oxford University Press, 1987, Chapter 1, <https://www.science.smith.edu/~jorourke/books/ArtGalleryTheorems/Art_Gallery_Chapter_1.pdf>: Section 1.3.1, the existence of an internal diagonal at a convex vertex used in the proof of Theorem 1.2
