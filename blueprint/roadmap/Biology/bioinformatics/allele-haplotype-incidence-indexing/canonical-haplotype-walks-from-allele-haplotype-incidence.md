# Canonical haplotype walks from allele–haplotype incidence

Let $C$ be an ordered catalog of $S$ reference-anchored variant sites on a chromosome region; site $s$ has interval $I_s=[p_s,e_s]$ and allele set $\mathcal A_s=\{\mathrm{REF},\mathrm{ALT}_1,\dots,\mathrm{ALT}_{m_s}\}$. For a fixed set $H$ of phased haplotypes, the incidence $x_{s,a,h}\in\{0,1\}$ records whether haplotype $h$ carries allele $a$ at $s$, and the H1 row of a nonreference allele is its carrier set $R_{s,a}=\{h:x_{s,a,h}=1\}$.

**Boundary-edge graph.** Let $B=\{b_0<\dots<b_t\}$ consist of the region start, the region end plus one, and every $p_s$ and $e_s+1$. Add a reference edge $b_i\to b_{i+1}$ for each consecutive pair and, for each nonreference allele $a$ at $s$, a labeled vertex $v_{s,a}$ with edges $b(p_s)\to v_{s,a}\to b(e_s+1)$.

**Theorem (conditional reconstruction).** Suppose (i) the catalog and graph-construction rule are fixed and known; (ii) all intervals lie in the region and distinct sites are pairwise disjoint; (iii) every haplotype has exactly one explicit allele state at every site, under a consistent phase-label convention; (iv) every alternative is one atomic catalog allele, with no nested or rearranged traversal. Then $C$ and the complete incidence assignment determine one canonical contiguous walk per haplotype in the boundary-edge graph, and the per-site allele assignment is recovered from the walk by reading off its alternative branches. Hence valid assignments and canonical walks are in bijection.

**Proposition (no unconditional equivalence).** Without a fixed catalog, or with overlapping or rearranged variation, allele–haplotype incidence does not determine the node-labeled topology or the sequence content of a pangenome graph.

**Encoding cost.** A carrier set of size $k$ among $|H|$ haplotypes costs $k\lceil\log_2|H|\rceil$ bits as a sorted list and $|H|$ bits as a bitmap, so the two codes cross at $k^*\approx|H|/\lceil\log_2|H|\rceil$; for equally likely carrier subsets of fixed size, any lossless code needs at least $\log_2\binom{|H|}{k}$ bits per row.

## Expansion

The proof is an induction over sites ordered by start coordinate: disjointness guarantees that the end boundary of one site precedes the start of the next, so from each site's end the reference edges lead uniquely to the next site, where the incidence selects either the reference subwalk or exactly one two-edge detour. Each detour vertex is allele-specific, so the walk determines the assignment back. The counterexamples behind the proposition split or contract reference segments or relabel sequence without changing any carrier set, and overlapping alternatives need not define a coherent coordinate traversal. The crossover is between two specific code families, not an optimality statement, and the counting bound does not apply to multi-row files that share redundancy across sites.

## Sources

- R. Garrone, "Adaptive Allele-Haplotype Incidence Indexing for Pangenome Queries: Representation, Reconstruction, and Benchmarking", Sections 3–5 (Definition 1, Theorem 1, Proposition 1). <https://doi.org/10.48550/arXiv.2512.21320>
