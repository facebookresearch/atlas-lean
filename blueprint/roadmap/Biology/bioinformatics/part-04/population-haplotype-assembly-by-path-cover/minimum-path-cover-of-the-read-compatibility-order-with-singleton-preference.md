# Minimum path cover of the read compatibility order with singleton preference

**Setting.** Reads aligned to a reference cover sets of SNP columns. Two reads **conflict** if they share a SNP column with different alleles; the conflict graph $G_M$ has the reads as vertices and conflicts as edges, and a proper colouring of $G_M$ with the fewest colours assigns reads to the fewest haplotypes. A read is **redundant** if its SNPs are a subset of another read's and the two do not conflict; after masking redundant reads, the **block compatibility graph** $\vec G$ on the remaining reads (of a connected component) has an arc $x \to y$ when $x$ starts before $y$ and $x$, $y$ do not conflict. It is acyclic and transitive.

**Reduction.** In a transitive DAG, chains are paths, so a minimum path cover of $\vec G$ is a minimum clique cover of the (undirected) compatibility graph, i.e. a minimum colouring of the conflict component; by Dilworth's theorem its size is the maximum number of pairwise conflicting reads.

**Theorem.** Let $\vec G$ have $n$ nodes and let $B^\varepsilon$ be the bipartite graph with a left copy $x_l$ and a right copy $x_r$ of every node, an edge $x_l y_r$ of weight $1$ for every arc $x \to y$ of $\vec G$, and an edge $x_l x_r$ of weight $1/(n+1)$ for every node. Take a maximum-weight matching of $B^\varepsilon$, contract each pair $x_l, x_r$, and take connected components. The result is a minimum path cover of $\vec G$ which, among minimum path covers, maximizes the number of single-node paths.

## Proof depends on

- [Dilworth's theorem](../../../../Combinatorics/partially-ordered-sets/dilworth-s-theorem/dilworth-decomposition.md)

## Expansion

In the unweighted "connects-to" bipartite graph, a matching with $k$ edges corresponds to a set of arcs with in- and out-degree at most one, i.e. to a path cover with $n - k$ paths, so a maximum matching gives a minimum path cover. With the light self-edges, a maximum-weight matching has total weight $k'$ with $k \le k' < k+1$ for the maximum unweighted matching size $k$, because $n$ light edges weigh less than one heavy edge; hence it still uses exactly $k$ heavy edges (the path count $n - k$ is unchanged) and uses the remaining weight to isolate as many reads as possible. Isolated reads are the likeliest to carry sequencing errors. Randomizing the node order before the Hungarian algorithm samples different optimal colourings, and reads always coloured alike are reported as one haplotype; a dynamic program over SNP loci then threads a consensus through the assembled haplotype regions with the fewest crossovers (minimum chimerism).

## Sources

- S. T. O'Neil, S. J. Emrich, "Haplotype and minimum-chimerism consensus determination using short sequence data", BMC Genomics 13(Suppl 2) (2012) S4, Related work and Methods (redundant reads; determination of block compatibility graphs), Theorem 1 and the minimum-chimerism dynamic program, <https://doi.org/10.1186/1471-2164-13-S2-S4>, PMCID PMC3394418.
