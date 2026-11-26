# Planar graphs have a vertex of degree at most five

In a simple planar graph with $n \ge 3$ vertices the vertex degrees sum to at most $6n - 12$. Consequently the average degree is less than $6$ and some vertex has degree at most $5$.

## Depends on

- [Straight-line planar graph](straight-line-planar-drawings/is-planar.md)

## Proof depends on

- [Edge and face bounds for planar graphs](edge-and-face-bounds-for-planar-graphs.md)

## Sources

- R. Diestel, *Graph Theory*, 6th ed., Graduate Texts in Mathematics 173, Springer, 2025, Chapter 4 (Planar graphs), <https://diestel-graph-theory.com/>: Corollary 4.2.10 (at most $3n - 6$ edges for $n \ge 3$ vertices), which bounds the degree sum by $6n - 12$
- *Computational Geometry*, lecture notes, ETH Zürich, autumn 2013, Chapter 4 (Plane graphs and the DCEL), <https://ti.inf.ethz.ch/ew/courses/CG13/lecture/Chapter%204.pdf>: Exercise 4.3 (every planar graph has a vertex of degree at most 5), stated as a consequence of Lemma 4.1
- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 22, proof of the independent-set lemma: in a triangulated planar graph $\sum_v \deg(v) = 2e = 6n - 12 < 6n$
