# Additive fits over all loci err by at least the dominance variance

Let $L$ be a finite set of loci and $A_l$ a finite set of alleles at locus $l$, let $p_l$ be allele
frequencies, $p_l(a) \ge 0$ and $\sum_{a \in A_l} p_l(a) = 1$, and let the real genotypic values be
symmetric, $G_l(i, j) = G_l(j, i)$. Then for every real $c$ and all functions
$a_l : A_l \to \mathbb{R}$,

$$V_D \le \sum_g f(g) \Bigl(G(g) - c - \sum_{l \in L} \bigl(a_l(i_l) + a_l(j_l)\bigr)\Bigr)^2,$$

summed over all ordered multilocus genotypes $g$, with $g_l = (i_l, j_l)$, where $f(g)$ is their
[frequency](geno-freq.md), $G(g)$ their [genotypic value](total-value.md) and $V_D$ the
[multilocus dominance variance](multi-dom-var.md): no function additive over all genes at all loci
fits the genotypic value with a smaller mean squared error (Fisher 1918).
