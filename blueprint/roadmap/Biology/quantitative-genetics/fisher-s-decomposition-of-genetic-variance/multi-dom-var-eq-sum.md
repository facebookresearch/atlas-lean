# For normalized weights the dominance variance is a sum over loci

Let $L$ be a finite set of loci and $A_l$ a finite set of alleles at locus $l$, and let the real
allele weights $p_l$ satisfy $\sum_{a \in A_l} p_l(a) = 1$ at every locus $l$; no sign condition is
needed. Then for all real genotypic values $G_l$ the
[multilocus dominance variance](multi-dom-var.md) $V_D$ is the sum of the one-locus
[dominance variances](dom-var.md) $V_{D,l}$ of $p_l$ and $G_l$:

$$V_D = \sum_{l \in L} V_{D,l}.$$
