# Multilocus parent–offspring covariance

Let $L$ be a finite set of loci, $A_l$ a finite set of alleles at locus $l$,
$p_l : A_l \to \mathbb{R}$ real allele weights and $G_l(i, j)$ real genotypic values of the ordered
one-locus genotypes $(i, j)$. Let $\mu$ be the [multilocus mean](multi-mean.md). A configuration $x$
gives every locus $l$ the parent's ordered genotype $(i_l, j_l)$, a gene $k_l$ from the mate and a
choice $b_l \in \{1, 2\}$ of the transmitted parental gene, $t_l = i_l$ if $b_l = 1$ and $t_l = j_l$
if $b_l = 2$. Put

$$
C_{PO} = \sum_x \prod_{l \in L} \frac{p_l(i_l)\, p_l(j_l)\, p_l(k_l)}{2}
\Bigl(\sum_{l} G_l(i_l, j_l) - \mu\Bigr) \Bigl(\sum_{l} G_l(t_l, k_l) - \mu\Bigr).
$$

When every $p_l$ is a probability vector, it is the covariance of the genotypic values of a parent
and its offspring: the parent is drawn in Hardy–Weinberg proportions and linkage equilibrium, each
locus transmits one of the parent's two genes with probability $1/2$, independently of the other
loci (unlinked loci), and the offspring's other gene at each locus comes from an unrelated mate.
