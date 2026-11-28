# Trans-ethnic LD score regression of z-score products

Let two populations $p = 1, 2$ have GWAS of the same trait with sample sizes $N_1, N_2$ and no sample overlap. Model each SNP $k$ as having per-allele causal effects $(\beta_{1k}, \beta_{2k})$ in the two populations, with genotype standard deviations $\sigma_{pk}$, LD (Pearson correlation) $r_{pjk}$ between SNPs $j$ and $k$ in population $p$, and annotations $a_C(k)$ (binary or continuous) for categories $C$. Treat the causal effects as random: $\mathbb E[\beta_{pk}] = 0$, effects at distinct SNPs are uncorrelated within and across populations, $\operatorname{Cov}(\beta_{pk}, \beta_{p'l}) = 0$ for $k \ne l$ and all $p, p'$, and the effects are independent of the sampling noise. Assume the per-SNP trans-ethnic covariance of causal effects is linear in the annotations,

$$\operatorname{Cov}(\beta_{1k}, \beta_{2k}) = \sum_C a_C(k)\,\theta_C .$$

Approximate the marginal z-score of SNP $j$ in population $p$, for small effects and standardized genotypes, by

$$Z_{pj} = \sqrt{N_p}\sum_k r_{pjk}\,\sigma_{pk}\beta_{pk} + e_{pj},$$

with sampling noise $e_{pj}$ of mean zero, independent of the effects and, because the samples do not overlap, independent between the two populations. Under this approximation the product of marginal z-scores of SNP $j$ satisfies

$$\mathbb E\bigl[Z_{1j}Z_{2j}\bigr] = \sqrt{N_1N_2}\sum_C \ell_\times(j, C)\,\theta_C, \qquad
\ell_\times(j, C) = \sum_k r_{1jk}\,r_{2jk}\,\sigma_{1k}\sigma_{2k}\,a_C(k),$$

so for the actual marginal statistics the identity holds approximately, to the accuracy of the marginal-score approximation; here $\ell_\times(j,C)$ is the trans-ethnic LD score of SNP $j$ with respect to $C$, computed from population-matched reference panels. The coefficients $\theta_C$ are estimated by weighted least squares of $Z_{1j}Z_{2j}$ on the $\ell_\times(j,C)$. The trans-ethnic genetic covariance of a binary annotation $C$ is then

$$\rho_g(C) = \sum_{j \in C}\sum_{C'} a_{C'}(j)\,\theta_{C'},$$

summing the fitted per-SNP covariances over the SNPs in $C$ using all annotations $C'$ in the model; population-specific heritabilities $h^2_{g1}(C), h^2_{g2}(C)$ are obtained the same way from single-population LD score regressions.

## Depends on

- [Random-effects model of stratified LD-score regression](../model.md)

## Expansion

Multiplying the two populations' expressions gives a double sum $N_1^{1/2}N_2^{1/2}\sum_{k}\sum_{l} r_{1jk}r_{2jl}\,\sigma_{1k}\sigma_{2l}\,\beta_{1k}\beta_{2l}$ plus terms containing the noise, where $\sigma_{pk}\beta_{pk}$ is SNP $k$'s per-standardized-genotype effect in population $p$. The noise terms have mean zero: $e_{1j}$ and $e_{2j}$ are independent of each other, because the samples do not overlap, and of the effects. In the double sum, $\mathbb E[\beta_{1k}\beta_{2l}] = \operatorname{Cov}(\beta_{1k}, \beta_{2l})$ because the effects are centred, and this vanishes for $k \ne l$ by the cross-SNP assumption; non-overlapping samples alone would not remove those terms, since they concern the effects and not the noise. What remains is $\sqrt{N_1N_2}\sum_k r_{1jk}r_{2jk}\sigma_{1k}\sigma_{2k}\operatorname{Cov}(\beta_{1k},\beta_{2k})$; substituting the linear annotation model yields the regression. A category is enriched for trans-ethnic covariance when SNPs in strong LD with it (in both populations) have larger z-score products. Modelling per-allele rather than per-standardized-genotype effects lets allele-frequency differences between populations enter through $\sigma_{pk}$ instead of being confused with effect-size differences.

## Sources

- H. Shi, S. Gazal, M. Kanai, E. M. Koch, et al., "Population-specific causal disease effect sizes in functionally important regions impacted by selection", Nature Communications 12 (2021), Results (Equation (1)) and Methods, <https://doi.org/10.1038/s41467-021-21286-1> (PMC7889654).
