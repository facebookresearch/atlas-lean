# Euclidean minimum spanning tree in O(n log n) time

The Euclidean minimum spanning tree of $n \ge 3$ points in $\mathbb{R}^2$, not all on one line, can be computed in $O(n \log n)$ time: compute the Voronoi diagram by Fortune's sweep and from it the Delaunay graph, its straight-line plane dual, which has $O(n)$ edges, and run Kruskal's algorithm on those edges (it uses only the order of the weights). This is correct because every edge $ab$ of a Euclidean minimum spanning tree is an edge of the Delaunay graph: a third site in the closed disk with diameter $ab$ would be strictly closer than $|ab|$ to both $a$ and $b$, and one of those two shorter edges would reconnect the two parts of the tree minus $ab$; so the midpoint of $ab$ has exactly $a$ and $b$ as nearest sites, and their Voronoi cells share an edge, also when four or more sites are cocircular. Running Kruskal's algorithm on all $\binom n2$ pairs takes $O(n^2 \log n)$ time.

## Depends on

- [The Delaunay graph is dual to the Voronoi diagram](the-delaunay-graph-is-dual-to-the-voronoi-diagram.md)
- [Euclidean minimum spanning trees lie in the Delaunay triangulation](euclidean-minimum-spanning-trees-lie-in-the-delaunay-triangulation.md)

## Proof depends on

- [Edge and face bounds for planar graphs](../../../GraphTheory/planar-graphs-and-minors/edge-and-face-bounds-for-planar-graphs.md)
- [Kruskal's algorithm gives a minimum spanning forest](../../graph-algorithms/spanning-trees-flows-matchings/kruskal-s-algorithm/kruskal-minimal.md)
- [Fortune's algorithm](../voronoi-diagrams/fortune-s-algorithm.md)
- [The Delaunay graph is dual to the Voronoi diagram](the-delaunay-graph-is-dual-to-the-voronoi-diagram.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 12, "Euclidean Minimum Spanning Tree": the $O(n \log n)$ algorithm via the Delaunay triangulation and Kruskal's algorithm, and the brute-force $O(n^2 \log n)$ bound
