# Multilocus breeding value

Let $L$ be a finite set of loci, $A_l$ a finite set of alleles at locus $l$,
$p_l : A_l \to \mathbb{R}$ real allele weights and $G_l(i, j)$ real genotypic values of the ordered
one-locus genotypes $(i, j)$. Let $\alpha_l$ be the one-locus [average effects](avg-effect.md) of
$p_l$ and $G_l$. The breeding value of the ordered multilocus genotype $g$, with $g_l = (i_l, j_l)$,
is the sum over loci of the average effects of its two genes:

$$B(g) = \sum_{l \in L} \bigl(\alpha_l(i_l) + \alpha_l(j_l)\bigr).$$
