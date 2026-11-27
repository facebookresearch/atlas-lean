# Euclidean minimum spanning tree in O(n log n) time

The Euclidean minimum spanning tree of $n \ge 3$ points in $\mathbb{R}^2$, not all on one line, can be computed in $O(n \log n)$ time: compute a Delaunay triangulation, which has $O(n)$ edges, and run Kruskal's algorithm on its edges (it uses only the order of the weights). This is correct because the Euclidean minimum spanning tree is a subgraph of the Delaunay triangulation, whereas running Kruskal's algorithm on all $\binom n2$ pairs takes $O(n^2 \log n)$ time.

## Depends on

- [Delaunay triangulation](delaunay-triangulation.md)
- [Euclidean minimum spanning trees lie in the Delaunay triangulation](euclidean-minimum-spanning-trees-lie-in-the-delaunay-triangulation.md)

## Proof depends on

- [Euclidean minimum spanning trees lie in the Delaunay triangulation](euclidean-minimum-spanning-trees-lie-in-the-delaunay-triangulation.md)
- [Number of triangles and edges of a triangulation](number-of-triangles-and-edges-of-a-triangulation.md)
- [Kruskal's algorithm gives a minimum spanning forest](../../graph-algorithms/spanning-trees-flows-matchings/kruskal-s-algorithm/kruskal-minimal.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 12, "Euclidean Minimum Spanning Tree": the $O(n \log n)$ algorithm via the Delaunay triangulation and Kruskal's algorithm, and the brute-force $O(n^2 \log n)$ bound
