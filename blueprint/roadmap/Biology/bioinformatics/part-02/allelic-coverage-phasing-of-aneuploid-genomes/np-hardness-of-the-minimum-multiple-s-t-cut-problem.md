# NP-hardness of the minimum multiple s-t cut problem

**Problem (Minimum Multiple s-t Cut).** Input: an undirected graph $G=(V,E)$ with nonnegative edge weights, whose vertex set is partitioned into $n$ pairs $\{v_i^a,v_i^b\}$. Output: a set $S\subseteq V$ containing exactly one vertex of each pair, minimizing the total weight of edges with one endpoint in $S$ and the other in $V\setminus S$.

In haplotype assembly each pair represents the two alleles of a heterozygous SNP, an edge weight measures support for two alleles lying on the same haplotype, and $S$ is one haplotype; edges of infinite weight join alleles already phased together, so any finite-weight solution respects existing haplotype fragments.

**Statement.** Minimum Multiple s-t Cut is NP-hard.

## Expansion

Reduce from Max-Cut with nonnegative weights. Given $G'=(V',E')$, create a pair $\{v_i^a,v_i^b\}$ for each $v_i'$ and, for each edge $(v_i',v_j')$ of weight $w$ ($i<j$), an edge $(v_i^a,v_j^b)$ of weight $w$. For a cut $\{S',V'\setminus S'\}$ put $S=\{v_i^a:v_i'\in S'\}\cup\{v_i^b:v_i'\notin S'\}$. The edge $(v_i^a,v_j^b)$ crosses $S$ exactly when $v_i'$ and $v_j'$ lie on the same side of the cut, so the crossing weight equals the total weight minus the cut weight. Minimizing one maximizes the other, and the correspondence is a bijection between feasible solutions. This justifies heuristic solvers, such as a Karger-type contraction that fixes the relative phase of two SNP pairs at a time, picking pairs in order of reliability $1/(-r_1\log r_1-r_2\log r_2)$, where $r_1$ and $r_2=1-r_1$ are the weight fractions supporting the two relative phases.

## Sources

- Pan W, Gong D, Sun D, Luo H. HICANCER: accurate and complete cancer genome phasing with Hi-C reads. *Scientific Reports* 11 (2021) 6609. <https://doi.org/10.1038/s41598-021-86104-6>. PMCID: PMC7987978. Methods, Definition 1, Theorem 1.
