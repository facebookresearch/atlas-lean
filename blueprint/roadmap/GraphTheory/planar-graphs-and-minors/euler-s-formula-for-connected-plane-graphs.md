# Euler's formula for connected plane graphs

Let $G$ be a connected simple graph with $v \ge 1$ vertices and $e$ edges, drawn in $\mathbb{R}^2$ as a straight-line plane graph: distinct vertices are distinct points, each edge is the closed segment between its endpoints, and two edges meet only in common endpoints. The *faces* of the drawing are the connected components of the complement in $\mathbb{R}^2$ of the union of its vertices and edges, the unbounded component included. If $f$ is the number of faces, then

$$v - e + f = 2.$$

## Depends on

- [Straight-line planar graph](straight-line-planar-drawings/is-planar.md)

## Expansion

This page becomes ready once:

- Proof prerequisite: the Jordan curve theorem for simple polygons (a simple closed polygonal curve separates the plane into exactly two components), which the cycle-adding step of the induction on $e - v + 1$ uses.
- The combinatorial form [Euler's formula](euler-s-formula-and-cycle-rank/euler-general.md) defines the face count from the cycle rank; connecting it to the faces of a drawing is the content of this page.

## Sources

- R. Diestel, *Graph Theory*, 6th ed., Graduate Texts in Mathematics 173, Springer, 2025, Chapter 4 (Planar graphs), <https://diestel-graph-theory.com/>: Theorem 4.2.9 (Euler's formula $n - m + \ell = 2$ for a connected plane graph, whose edges are polygonal arcs)
- *Geometric Algorithms*, course slides, Utrecht University, 2023, "Voronoi diagrams", <https://ics-websites.science.uu.nl/docs/vakken/ga/2023/slides/slides7_combined.pdf>: slide 14 (Euler's formula for planar graphs: a connected planar graph with $n_v$ vertices, $n_e$ edges and $n_f$ faces satisfies $n_v - n_e + n_f = 2$)
- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 11, footnote to the size of the Voronoi diagram (Euler's formula $v - e + f = 2$ for planar graphs)
