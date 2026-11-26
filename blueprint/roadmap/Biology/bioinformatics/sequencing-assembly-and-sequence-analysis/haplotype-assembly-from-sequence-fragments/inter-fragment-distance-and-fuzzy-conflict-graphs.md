# Inter-fragment distance and fuzzy conflict graphs

**Setting.** A variant matrix $X\in\{0,1,-\}^{m\times n}$ records, for $m$ sequenced fragments $f_1,\dots,f_m$ of a diploid individual and $n$ heterozygous SNPs, the observed allele $x_{ij}\in\{0,1\}$ or $-$ when $f_i$ does not cover SNP $j$. Single individual haplotype reconstruction partitions the fragments into two sets $C_1,C_2$ and reads off haplotypes $h_1,h_2$ by column-wise majority, aiming at **minimum error correction** (MEC): the fewest allele flips making every fragment consistent with its haplotype, $\mathrm{MEC}=\sum_i\min\{d(f_i,h_1),d(f_i,h_2)\}$ with $d$ the Hamming distance on covered sites. Optimal MEC is NP-hard.

**Inter-fragment distance.** For $x,y\in\{0,1,-\}$ let $x\otimes y=0$ if $x=y\in\{0,1\}$, $1$ if $x\ne y$ with $x,y\in\{0,1\}$, and $\tfrac12$ otherwise. The distance between fragments is

$$\Delta(f_i,f_k)=\frac1{T_{ik}}\sum_{j}x_{ij}\otimes x_{kj}\in[0,1],$$

where the sum runs over the $T_{ik}$ SNPs covered by $f_i$ or $f_k$. The **pivot** value $\lambda=\tfrac12$ is the distance of two fragments that share no covered SNP: such a pair carries no information on whether they belong to the same haplotype, while $\Delta<\tfrac12$ favours the same haplotype and $\Delta>\tfrac12$ opposite haplotypes.

**Fuzzy conflict graph.** The complete graph on the fragments with edge weights $\Delta(f_i,f_k)$. It refines the binary conflict graph (an edge for at least one mismatch): for $f_1=000$, $f_8=111$, $f_{10}=010$ on the same three sites the weights are $1$, $\tfrac13$ and $\tfrac23$, so $f_1$ and $f_{10}$ are grouped together. Dividing the fragments into two maximally dissimilar groups is a weighted max-cut on this graph; a uniformly random cut already has expected weight $\tfrac12\sum_lw_l\ge\tfrac12\mathrm{OPT}$.

## Expansion

Missing alleles contribute exactly the pivot value $\tfrac12$, so they neither push fragments together nor apart, and the normalization by $T_{ik}$ makes fragments of different lengths comparable. The FastHap heuristic deletes pivot-weight edges, seeds the two groups with the endpoints of the heaviest edge, and repeatedly assigns the fragment with the most decisive distances to the group it is least dissimilar to; a final refinement step moves fragments between groups whenever this lowers the MEC of the majority haplotypes. Because max-cut is NP-hard even with unit weights, the gain over generic approximation comes from exploiting the pivot structure of the weights.

## Sources

- S. Mazrouee and W. Wang, "FastHap: fast and accurate single individual haplotype reconstruction using fuzzy conflict graphs", Bioinformatics 30(17) (2014) i371–i378, <https://doi.org/10.1093/bioinformatics/btu442>, PMCID PMC4147895. Section 2.1, Eq. (1)–(3), Definitions 1–3 and Algorithm 2.
