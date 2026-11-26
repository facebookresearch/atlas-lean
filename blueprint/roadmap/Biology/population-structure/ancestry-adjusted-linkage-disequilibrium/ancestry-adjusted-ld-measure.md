# Ancestry-adjusted linkage disequilibrium in structured populations

Consider two biallelic sites $s, t$. In a homogeneous population with haplotype probability $p_{st}$ of carrying both reference alleles and marginal reference-allele probabilities $p_s, p_t$, the **standard LD** is $(D_{\mathrm{std}})_{st} = p_{st} - p_s p_t$, with squared correlation $(\rho^2_{\mathrm{std}})_{st} = (D_{\mathrm{std}})_{st}^2 / ((D_{\mathrm{std}})_{ss} (D_{\mathrm{std}})_{tt})$.

In a structured or admixed sample of $n$ diploid individuals, let individual $i$ have its own haplotype parameters $\mathbf{p}^i_{st} = (p^i_{st}, p^i_s, p^i_t)$, and let $G_{is}, G_{it} \in \{0, 1, 2\}$ be its reference-allele counts, each the sum of two independent, identically distributed parental haplotype contributions. Then $\operatorname{Cov}(G_{is}, G_{it} \mid \mathbf{p}^i_{st}) = 2(p^i_{st} - p^i_s p^i_t)$.

**Definitions (Bercovich et al.).** The ancestry-adjusted **sample LD** and **population LD** are
$$(D^n_{\mathrm{adj}})_{st} = \frac{1}{2n} \sum_{i=1}^{n} \operatorname{Cov}(G_{is}, G_{it} \mid \mathbf{p}^i_{st}) = \frac{1}{n} \sum_{i=1}^{n} \big(p^i_{st} - p^i_s p^i_t\big), \qquad (D_{\mathrm{adj}})_{st} = \tfrac12\, \mathbb{E}\big[\operatorname{Cov}(G_s, G_t \mid \mathbf{p}_{st})\big],$$
where in the second the individual parameters $\mathbf{p}_{st}$ are drawn from a population distribution $P_{st}$. By the law of large numbers $(D^n_{\mathrm{adj}})_{st} \to (D_{\mathrm{adj}})_{st}$ as $n \to \infty$; if $P_{st}$ is degenerate (a homogeneous population), $D_{\mathrm{adj}} = D_{\mathrm{std}}$.

**Theorem (Bercovich et al., Theorem 1).** Suppose the population is made of $k$ source sub-populations with standard LD $(D^{\ell}_{\mathrm{std}})_{st}$, $\ell = 1, \dots, k$, and let $w^{\ell}_{st}$ be the probability that both alleles of a haplotype at $s$ and $t$ derive from sub-population $\ell$. Then $\sum_{\ell} w^{\ell}_{st} \le 1$,
$$(D_{\mathrm{adj}})_{st} = \sum_{\ell=1}^{k} w^{\ell}_{st}\, (D^{\ell}_{\mathrm{std}})_{st}, \qquad (D_{\mathrm{adj}})^2_{st} \le \sum_{\ell=1}^{k} w^{\ell}_{st}\, (D^{\ell}_{\mathrm{std}})^2_{st}.$$
In particular, unlike $D_{\mathrm{std}}$ computed on the pooled sample, $D_{\mathrm{adj}}$ creates no spurious LD between unlinked sites that differ in frequency between sub-populations: if every $D^{\ell}_{\mathrm{std}} = 0$, then $D_{\mathrm{adj}} = 0$. For $k$ separate sub-populations with relative sizes $w_\ell$, $(D_{\mathrm{adj}})_{st} = \sum_\ell w_\ell (D^{\ell}_{\mathrm{std}})_{st}$.

## Depends on

- [Linkage disequilibrium of a two-locus gamete law](../../population-genetics/linkage-disequilibrium-and-haldane-s-map-functio/linkage-diseq.md)

## Expansion

Within an individual, covariance is computed conditional on that individual's ancestry-specific allele frequencies, so the between-individual variation in frequencies (which inflates pooled covariances, the classical admixture LD) is removed before averaging. Conditioning a haplotype's pair of alleles on their joint ancestry decomposes the covariance into within-ancestry covariances weighted by $w^{\ell}_{st}$; pairs whose two alleles come from different sources contribute zero covariance because the two sources are independent, which is why the weights can sum to less than one. The squared bound is Jensen's inequality for the convex function $x \mapsto x^2$.

## Sources

- U. Bercovich, M. S. Rasmussen, Z. Li, C. Wiuf and A. Albrechtsen, "Measuring linkage disequilibrium and improvement of pruning and clumping in structured populations", Genetics 229 (2025), iyaf009, <https://doi.org/10.1093/genetics/iyaf009>; preprint bioRxiv (2024), Methods, Eqs. 1–5 and Theorem 1, <https://doi.org/10.1101/2024.05.02.592187>.
