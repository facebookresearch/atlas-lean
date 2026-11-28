# EdgeSearch algorithm for maximal triangularly connected subgraphs

Let $G$ be the [symmetric best-hit graph](triangularly-connected-subgraphs-of-a-symmetric-best-hit-graph.md)
of $g$ genomes. The EdgeSearch algorithm is:

1. Take an unprocessed edge of $G$ and initialize a cluster $C$ with this edge and its endpoints.
2. For each unprocessed edge $(u, v)$ of $C$: for every vertex $w$ such that $(u, w)$ and
   $(v, w)$ are unprocessed edges of $G$, at least one of them not yet in $C$, add $w$, $(u, w)$
   and $(v, w)$ to $C$; then mark $(u, v)$ processed.
3. When $C$ has no unprocessed edges, output $C$ if it has at least three vertices, and return to
   step 1 until every edge is processed.

**Theorem.** EdgeSearch outputs exactly the maximal triangularly connected subgraphs of $G$ that
are not single edges (the COGs), and its worst-case running time is $O(g^3 \log g)$ for a fixed
maximum genome size, compared with $O(g^6)$ for merging clusters by iterating over pairs of
triangles.

## Depends on

- [Triangularly connected subgraphs of a symmetric best-hit graph](triangularly-connected-subgraphs-of-a-symmetric-best-hit-graph.md)

## Expansion

Correctness follows in four steps. The clusters are edge-disjoint, because a cluster is not closed
until all its edges are processed, so every triangle containing one of its edges has been absorbed
into it. Every triangle is found and assigned to exactly one cluster, because every edge is
eventually processed and clusters are edge-disjoint. Each cluster is triangularly connected,
because it grows only by triangles sharing an edge with a triangle already in it. Each cluster is
maximal, because a triangle-path leaving it would need a triangle sharing an edge with it, and that
triangle would have been absorbed. For the running time, there are $O(g^2)$ edges to process; for
each, candidate third vertices $w$ are scanned over the $O(g)$ other genomes, and adjacency of the
remaining pair is checked in $O(\log g)$ from a sorted adjacency list. The triangle-merging
approach instead starts from up to $O(g^3)$ triangles and compares each cluster with each triangle.

## Sources

- D. M. Kristensen, L. Kannan, M. K. Coleman, Y. I. Wolf, A. Sorokin, E. V. Koonin, A. Mushegian,
  "A low-polynomial algorithm for assembling clusters of orthologous groups from intergenomic
  symmetric best matches", Bioinformatics 26 (2010), Section 2.1, "Theory" (EdgeSearch algorithm, Theorem and proof, complexity analysis),
  <https://doi.org/10.1093/bioinformatics/btq229> (PMC2881409).
