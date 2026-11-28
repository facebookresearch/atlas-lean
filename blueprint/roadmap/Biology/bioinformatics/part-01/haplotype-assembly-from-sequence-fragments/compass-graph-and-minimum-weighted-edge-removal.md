# Compass graph and minimum weighted edge removal

**SNP–fragment matrix.** Let $M$ be an $m \times n$ matrix over $\{0, 1, -\}$ whose rows are sequence fragments (reads with non-polymorphic bases removed) and whose columns are heterozygous SNPs, with $M_{ik} \in \{0,1\}$ the allele read by fragment $i$ at SNP $k$ and $M_{ik} = -$ if fragment $i$ does not cover SNP $k$. Fragments $i \ne j$ are in **fragment conflict** if

$$\exists\, k:\ M_{ik} \ne -,\ M_{jk} \ne -,\ M_{ik} \ne M_{jk}.$$

The **fragment conflict graph** $G_F$ has a vertex per fragment and an edge per conflicting pair. Without sequencing errors the fragments split into two haplotype classes, and $M$ is called **feasible** when $G_F$ is bipartite.

**Compass graph.** The compass graph $G_C$ has a vertex per SNP and an edge $e = \{k, l\}$ whenever some fragment covers both SNPs. Let $n_{ab}(e)$ be the number of fragments reading alleles $a$ at $k$ and $b$ at $l$, and give $e$ the weight

$$w(e) = \big(n_{00}(e) + n_{11}(e)\big) - \big(n_{01}(e) + n_{10}(e)\big),$$

so $w(e) > 0$ favours the in-phase relation ($k$, $l$ carry equal alleles on each haplotype) and $w(e) < 0$ the out-of-phase relation. Any spanning tree of a connected $G_C$ determines a unique phasing by propagating majority-rule edge relations.

**Proposition (conflicting cycles).** A simple cycle of $G_C$ is **conflicting**, meaning two paths around it between the same vertices imply different phasings, if and only if it contains an edge of weight $0$ or an odd number of edges of negative weight.

**Theorem (hardness).** The *minimum weighted edge removal* (MWER) problem, remove a set of edges of $G_C$ of minimum total $|w|$ so that no conflicting cycle remains, is NP-hard; so is the analogous minimum weighted vertex removal problem. Both lie in NP.

## Expansion

Composing relations around a cycle multiplies signs: an in-phase edge acts as $+1$, an out-of-phase edge as $-1$, and a cycle is consistent exactly when the product is $+1$, i.e. when the number of negative edges is even; a zero-weight edge gives no relation at all. Hardness is shown by reduction from the problem of deleting the fewest edges of a graph $G$ to make it bipartite. Every graph is the fragment conflict graph of some SNP–fragment matrix (one fragment per vertex and, for each edge, a new SNP read with opposite alleles by its two endpoints); for that matrix $G_C$ is the line graph of $G_F$, odd cycles of $G_F$ correspond one-to-one to conflicting cycles of $G_C$, and so $G_C$ has no conflicting cycle exactly when $G_F$ is bipartite. Subdividing edges and assigning large weights to clique edges created by high-degree vertices makes an optimal MWER solution delete only edges that encode edges of $G$. These results justify heuristics that work on a spanning-tree cycle basis, repeatedly removing low-$|w|$ edges (or flipping fragment alleles, for minimum error correction) from conflicting basis cycles; the framework extends to two individuals sharing an identical-by-descent tract and to polyploid genomes with more than two haplotypes.

## Sources

- D. Aguiar and S. Istrail, "Haplotype assembly in polyploid genomes and identical by descent shared tracts", Bioinformatics 29 (2013), i352–i360, Section 2 (Eq. (1), Section 2.1) and Section 3.1 (Lemmas 1–4, Corollary 1, Theorems 1–2), <https://doi.org/10.1093/bioinformatics/btt213>, PMCID: PMC3694639.
- D. Aguiar and S. Istrail, "HapCompass: a fast cycle basis algorithm for accurate haplotype assembly of sequence data", Journal of Computational Biology 19 (2012), 577–590, <https://doi.org/10.1089/cmb.2012.0084>.
- R. Lippert, R. Schwartz, G. Lancia and S. Istrail, "Algorithmic strategies for the single nucleotide polymorphism haplotype assembly problem", Briefings in Bioinformatics 3 (2002), 23–31.
