# NP-hardness of the smallest sub-DAG problem

After contigs are placed on unified optical-map coordinates, overlaps between contigs (oriented left to right) form a directed acyclic **overlap graph**. A minimum tiling path is a smallest set of contigs that still covers the same genomic span; on a connected component with one source and one sink it is a shortest source-to-sink path, but alignment errors can create several sources and sinks.

**Smallest sub-DAG problem.** Input: a connected directed acyclic graph $G = (V, E)$ with source set $S$ and sink set $T$. Output: a subgraph $G' = (V', E')$ of $G$ that is a connected directed acyclic graph with $S \subseteq V'$ and $T \subseteq V'$ and with $|V'|$ minimum among all such subgraphs.

**Theorem.** The smallest sub-DAG problem is NP-hard.

## Proof depends on

- [SET COVER is NP-complete](../../../../TheoryOfComputation/np-completeness/set-systems-and-location/set-cover/set-cover-np-complete.md)

## Expansion

The proof is a polynomial reduction from Set Cover. Given a universe $U$ and a family $\mathcal{C}$ of subsets, build one vertex per element of $U$ (these are the sinks), one vertex per set in $\mathcal{C}$, and a single source $s$. Add an arc from $s$ to every set vertex and an arc from a set vertex $c$ to an element vertex $e$ whenever $e \in c$. Any connected sub-DAG containing $s$ and all sinks must reach each element through some set vertex containing it, so its set vertices form a set cover; conversely a set cover of size $k$ yields such a sub-DAG on $1 + k + |U|$ vertices. Minimizing $|V'|$ therefore minimizes the cover size. Because of this hardness, the minimum tiling path is computed heuristically: take the shortest of all source-to-sink shortest paths, then repeatedly attach uncovered sources and sinks to the current sub-DAG by shortest paths.

## Sources

- W. Pan, S. I. Wanamaker, A. M. V. Ah-Fong, H. S. Judelson, S. Lonardi, "Novo&Stitch: accurate reconciliation of genome assemblies via optical maps", Bioinformatics (2018), Section 3.1.1 (conflict hypergraph, integer program, Theorem 1) and Section 3.1.2 (Definition 2, Theorem 3). <https://doi.org/10.1093/bioinformatics/bty255> (PMC6022655)
