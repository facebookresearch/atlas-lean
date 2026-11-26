# Region-weight characterization of Gabriel haplotype blocks

**Pair classification.** For SNPs $g_u, g_v$ let $[C_L, C_U]$ be a 90% confidence interval for $|D'|$. The pair is in **strong LD** if $C_L \ge 0.7$ and $C_U \ge 0.98$; it shows **strong evidence of historical recombination (EHR)** if $C_U < 0.9$; otherwise it is non-informative. Informative pairs are those in strong LD or strong EHR.

**Haplotype block (Gabriel et al.).** Let $C = \langle g_1, \dots, g_n\rangle$ be a chromosome and $G = \langle g_i, \dots, g_j\rangle$ a region of adjacent SNPs containing $l$ strong-LD pairs and $r$ strong-EHR pairs. For a threshold $d \in (0,1)$ (classically $d = 0.95$), $G$ is a haplotype block if (a) the outermost SNPs $g_i, g_j$ are in strong LD and (b) $l/(l+r) \ge d$.

**Weights.** Define the SNP-pair weight

$$w(u, v) = \begin{cases} 1 - d & \text{strong LD},\\ -d & \text{strong EHR},\\ 0 & \text{non-informative},\end{cases}$$

and the region weight $\bar w(i, j) = \sum_{v=i+1}^{j}\sum_{u=i}^{v-1} w(u, v)$, the sum over all pairs inside $G$.

**Theorem.** $G = \langle g_i, \dots, g_j\rangle$ is a haplotype block if and only if $w(i, j) = 1 - d$ and $\bar w(i, j) \ge 0$.

**Incremental computation.** Region weights satisfy

$$\bar w(i, j) = \bar w(i, j-1) + \sum_{u=i}^{j-1} w(u, j),$$

so scanning SNPs left to right and keeping one running weight $W[i] = \bar w(i, j)$ per start position finds all candidate blocks with $\Theta(n)$ memory instead of an $n \times n$ confidence-interval matrix. **Pruning:** the weight of any extension $\langle g_i, \dots, g_k\rangle$, $k > j$, is at most $\bar w(i, j) + (1-d)\big[\binom{k-i+1}{2} - \binom{j-i+1}{2}\big]$ (all new pairs in strong LD); if this bound is negative for every admissible $k$, no block can start at $g_i$ and end beyond $g_j$, so pair weights $w(u, j')$ with $u$ left of the smallest still-viable start need not be computed. Selecting non-overlapping candidates by decreasing length, as in the classical two-step procedure, then yields exactly the same partition.

## Expansion

The theorem is a one-line rewriting: a region with $S$ pairs, of which $l$ are strong LD and $r$ strong EHR, has $\bar w = l(1-d) - rd + 0 \cdot (S - l - r) = l - d(l + r)$, and $l - d(l+r) \ge 0 \iff l/(l+r) \ge d$; condition (a) is $w(i,j) = 1 - d$. Turning the ratio condition into the sign of an additive score is what makes incremental updates and branch-and-bound pruning possible, because adding a SNP only adds the weights of its pairs with earlier SNPs. In practice more than 80% of pairwise LD computations are skipped, and a window-based iteration over the chromosome removes any cap on block length, revealing LD blocks spanning more than a megabase. Replacing likelihood-based confidence intervals for $D'$ with an approximate variance estimator gives further speed at the cost of exactness.

## Sources

- D. Taliun, J. Gamper, C. Pattaro, "Efficient haplotype block recognition of very long and dense genetic sequences", BMC Bioinformatics 15 (2014) 10, Methods (pair classification, Definitions 1–3, Theorem 1 with proof, MIG and MIG+ algorithms), <https://doi.org/10.1186/1471-2105-15-10>.
- S. B. Gabriel, S. F. Schaffner, H. Nguyen, et al., "The structure of haplotype blocks in the human genome", Science 296 (2002) 2225–2229, <https://doi.org/10.1126/science.1069424>.
