# For normalized weights the genetic variance is a sum over loci

Let $L$ be a finite set of loci and $A_l$ a finite set of alleles at locus $l$, and let the real
allele weights $p_l$ satisfy $\sum_{a \in A_l} p_l(a) = 1$ at every locus $l$; no sign condition is
needed. Then for all real genotypic values $G_l$ the [multilocus genetic variance](multi-gen-var.md)
$V_G$ is the sum of the one-locus [genetic variances](gen-var.md) $V_{G,l}$ of $p_l$ and $G_l$:

$$V_G = \sum_{l \in L} V_{G,l}.$$
