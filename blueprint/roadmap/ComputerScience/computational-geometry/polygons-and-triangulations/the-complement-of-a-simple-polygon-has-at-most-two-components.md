# The complement of a simple polygon has at most two components

Let $P \subset \mathbb{R}^2$ be the boundary curve of a simple polygon, a closed polygonal curve without self-intersections. Then $\mathbb{R}^2 \setminus P$ has at most two connected components.

In the slab-decomposition proof, after a rotation of the plane (a homeomorphism) that gives the vertices distinct $x$-coordinates, the vertical lines through the vertices cut $\mathbb{R}^2 \setminus P$ into trapezoids (some unbounded or degenerate). Walking once around $P$ and recording the trapezoids immediately to the left of the walker visits every trapezoid labelled *left*, and consecutive trapezoids in this walk share a vertical wall; so the left trapezoids have a connected union, and symmetrically so do the right ones. Every trapezoid is labelled left or right.

## Depends on

- [Simple polygons](simple-polygons.md)

## Sources

- J. Erickson, *Computational Topology*, lecture notes, University of Illinois, 2023, Chapter 1 (Simple polygons), <https://jeffe.cs.illinois.edu/teaching/comptop/2023/notes/01-simple-polygons.pdf>: Section 1.2, Lemma $\le 2$ and its proof by the slab decomposition and the left/right labelling of trapezoids
