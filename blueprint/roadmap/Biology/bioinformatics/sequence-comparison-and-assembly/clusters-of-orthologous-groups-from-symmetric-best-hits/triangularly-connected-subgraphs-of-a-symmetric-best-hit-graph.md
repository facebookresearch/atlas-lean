# Triangularly connected subgraphs of a symmetric best-hit graph

Let $g$ genomes each contain at most $p$ genes (after collapsing lineage-specific in-paralogs into
single vertices). The symmetric best-hit graph $G$ has the genes as vertices and an edge between
genes of different genomes whenever each is the other's best match; $G$ is therefore $g$-partite.
It has $n \le gp$ vertices, at most $\binom{g}{2}p^2 = O(g^2)$ edges and at most
$\binom{g}{3}p^3 = O(g^3)$ triangles.

A *triangle-path* is a sequence of triangles $T_1, \dots, T_k$ of $G$ such that $T_i$ and
$T_{i+1}$ share exactly one edge for $1 \le i \le k-1$, and $T_i$ and $T_j$ share no edge for
$j > i+1$. A connected subgraph $C$ of $G$ is *triangularly connected* if for any two distinct
edges $e, e'$ of $C$ there is a triangle-path in $C$ whose first triangle contains $e$ and whose
last triangle contains $e'$. A cluster of orthologous groups (COG) is a maximal triangularly
connected subgraph of $G$ that is not a single edge. Distinct maximal triangularly connected
subgraphs are edge-disjoint, hence triangle-disjoint, and every triangle of $G$ lies in exactly
one COG.

## Expansion

The vertex bound holds because each genome contributes at most $p$ genes. An edge needs genes
from two different genomes and a triangle genes from three, which gives the edge and triangle
bounds; as $g$ grows with $p$ fixed, they are quadratic and cubic in $g$. Requiring triangles
rather than single edges guards against spurious best hits: three genes from three genomes that
are pairwise best matches are a robust signal of orthology, and a COG grows by adding triangles
that share a side with it. If two maximal triangularly connected subgraphs shared an edge, their
union would still be triangularly connected (paths through the shared edge join them), contradicting
maximality; this gives edge-disjointness, and since a triangle is determined by its edges, triangle
disjointness follows.

## Sources

- D. M. Kristensen, L. Kannan, M. K. Coleman, Y. I. Wolf, A. Sorokin, E. V. Koonin, A. Mushegian,
  "A low-polynomial algorithm for assembling clusters of orthologous groups from intergenomic
  symmetric best matches", Bioinformatics 26 (2010), Section 2.1, "Theory", <https://doi.org/10.1093/bioinformatics/btq229> (PMC2881409).
