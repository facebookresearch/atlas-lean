# Residual-covariance estimator of ancestry-adjusted LD and its consistency

Let $G \in \{0, 1, 2\}^{n \times m}$ be genotypes of $n$ individuals at $m$ SNPs with $G_{is} \sim \mathrm{Bin}(2, \Pi_{is})$, genotypes of different individuals independent given $\Pi$, and dependence allowed within an individual. Assume the admixture structure $\Pi = Q F$, where $Q \in [0,1]^{n \times k}$ has rank $k \le n$ and rows summing to one (admixture proportions) and $F \in [0,1]^{k \times m}$ holds ancestral allele frequencies. Let $P = Q (Q^{\top} Q)^{-1} Q^{\top}$ be the projection onto the column space of $Q$, $\hat P$ an estimate of it (for example from the leading $k$ principal components of $G$), $2\hat\Pi = \hat P G$, and $J$ the $n \times n$ all-ones matrix.

**Estimator (Bercovich et al., Eqs. 7–9).** With residuals $R = G - 2\hat\Pi$,

$$(\hat D_{\mathrm{adj}})_{st} = \frac{1}{2(n - k)} \sum_{i=1}^{n} (R_{is} - \bar R_{\cdot s})(R_{it} - \bar R_{\cdot t}), \qquad \hat D_{\mathrm{adj}} = \frac{1}{2(n-k)}\, G^{\top} (I - \hat P)(I - J/n)(I - \hat P)\, G,$$

and the adjusted squared correlation is $(r^2_{\mathrm{adj}})_{st} = (\hat D_{\mathrm{adj}})^2_{st} / ((\hat D_{\mathrm{adj}})_{ss} (\hat D_{\mathrm{adj}})_{tt})$. When $Q$ is known, $\hat D_{\mathrm{adj}} = \frac{1}{2(n-k)} G^{\top}(I - P) G$. For $k = 1$ this is the usual unphased-genotype (Burrows-type) estimator of $D_{\mathrm{std}}$; for $k$ discrete sub-populations it is the pooled within-group covariance.

**Theorem (Bercovich et al., Theorems 2–3).**
1. If $\hat P^{n,m} \to P$ as $m \to \infty$ with $n$ fixed, then $(\hat D^{n,m}_{\mathrm{adj}})_{st} \to \frac{1}{2(n-k)} G_{\cdot s}^{\top} (I - P) G_{\cdot t}$ and

$$\mathbb{E}\big[(\hat D^{n,m}_{\mathrm{adj}})_{st}\big] \to C_{st} = \frac{1}{2(n - k)} \sum_{i=1}^{n} (I - P)_{i\cdot}\, H_{st}\, (I - P)_{i\cdot}^{\top},$$

where $H_{st} = \operatorname{diag}\big(\operatorname{Cov}(G_{1s}, G_{1t}), \dots, \operatorname{Cov}(G_{ns}, G_{nt})\big)$ collects the within-individual LD. In particular, if $G_{\cdot s}$ and $G_{\cdot t}$ are independent, $\mathbb{E}[(\hat D^{n,m}_{\mathrm{adj}})_{st}] \to 0$. If $Q$ is known these hold with equality for every $m$.
2. If $Q$ is known (and admixture proportions are drawn from the population distribution as $n$ grows), then $(\hat D^{n,m}_{\mathrm{adj}})_{st} \to (D_{\mathrm{adj}})_{st}$ as $n \to \infty$, the population LD.

## Depends on

- [Ancestry-adjusted linkage disequilibrium in structured populations](ancestry-adjusted-ld-measure.md)

## Proof depends on

- [Ancestry-adjusted linkage disequilibrium in structured populations](ancestry-adjusted-ld-measure.md)
- [L² weak law of large numbers](../../../Probability/laws-of-large-numbers/l2-weak-law-of-large-numbers/l2-weak-law.md)

## Expansion

Since $\mathbb{E}[G \mid Q] = 2 Q F$ lies in the column space of $Q$, the residual $(I - P) G$ removes the structured mean exactly, so its columns have mean zero and the cross-product $G_{\cdot s}^{\top}(I - P)G_{\cdot t} = (G_{\cdot s} - 2\Pi_{\cdot s})^{\top} (I - P) (G_{\cdot t} - 2\Pi_{\cdot t})$ has expectation $\operatorname{tr}((I - P) H_{st})$ by independence across individuals. The factor $n - k$ is the residual degrees of freedom (Bessel-type correction), which makes the estimator unbiased for the sample LD when individuals share LD. Pruning or clumping SNPs with $r^2_{\mathrm{adj}}$ in place of pooled $r^2$ avoids discarding unlinked SNPs whose correlation is created purely by ancestry differences.

## Sources

- U. Bercovich, M. S. Rasmussen, Z. Li, C. Wiuf and A. Albrechtsen, "Measuring linkage disequilibrium and improvement of pruning and clumping in structured populations", Genetics 229 (2025), iyaf009, <https://doi.org/10.1093/genetics/iyaf009>; preprint bioRxiv (2024), Methods, Eqs. 6–11 and Theorems 2–3, <https://doi.org/10.1101/2024.05.02.592187>.
