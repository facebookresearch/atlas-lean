# Decomposition of a multilocus genotypic value for normalized weights

Let $L$ be a finite set of loci and $A_l$ a finite set of alleles at locus $l$, and let the real
allele weights $p_l$ satisfy $\sum_{a \in A_l} p_l(a) = 1$ at every locus $l$; no sign condition is
needed. Then for all real genotypic values $G_l$ and every ordered multilocus genotype $g$, with
$g_l = (i_l, j_l)$,

$$G(g) = \mu + B(g) + \sum_{l \in L} \delta_l(i_l, j_l),$$

where $G(g)$ is the [genotypic value](total-value.md), $\mu$ the [multilocus mean](multi-mean.md),
$B(g)$ the [breeding value](breeding-value.md) and $\delta_l$ the one-locus
[dominance deviations](dom-dev.md).
