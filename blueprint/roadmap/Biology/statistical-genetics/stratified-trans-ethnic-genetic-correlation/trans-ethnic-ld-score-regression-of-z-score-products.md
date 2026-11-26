# Trans-ethnic LD score regression of z-score products

Let two populations $p = 1, 2$ have GWAS of the same trait with sample sizes $N_1, N_2$ and no sample overlap. Model each SNP $k$ as having per-allele causal effects $(\beta_{1k}, \beta_{2k})$ in the two populations, with genotype standard deviations $\sigma_{pk}$, LD (Pearson correlation) $r_{pjk}$ between SNPs $j$ and $k$ in population $p$, and annotations $a_C(k)$ (binary or continuous) for categories $C$. Assume the per-SNP trans-ethnic covariance of causal effects is linear in the annotations,

$$\operatorname{Cov}(\beta_{1k}, \beta_{2k}) = \sum_C a_C(k)\,\theta_C .$$

Then the product of marginal z-scores of SNP $j$ satisfies

$$\mathbb E\bigl[Z_{1j}Z_{2j}\bigr] = \sqrt{N_1N_2}\sum_C \ell_\times(j, C)\,\theta_C, \qquad
\ell_\times(j, C) = \sum_k r_{1jk}\,r_{2jk}\,\sigma_{1k}\sigma_{2k}\,a_C(k),$$

where $\ell_\times(j,C)$ is the trans-ethnic LD score of SNP $j$ with respect to $C$, computed from population-matched reference panels. The coefficients $\theta_C$ are estimated by weighted least squares of $Z_{1j}Z_{2j}$ on the $\ell_\times(j,C)$. The trans-ethnic genetic covariance of a binary annotation $C$ is then

$$\rho_g(C) = \sum_{j \in C}\sum_{C'} a_{C'}(j)\,\theta_{C'},$$

summing the fitted per-SNP covariances over the SNPs in $C$ using all annotations $C'$ in the model; population-specific heritabilities $h^2_{g1}(C), h^2_{g2}(C)$ are obtained the same way from single-population LD score regressions.

## Depends on

- [Random-effects model of stratified LD-score regression](../stratified-ld-score-regression/model.md)

## Expansion

With standardized genotypes, $Z_{pj} \approx \sqrt{N_p}\sum_k r_{pjk}\,\sigma_{pk}\beta_{pk} + \text{noise}$, where $\sigma_{pk}\beta_{pk}$ is SNP $k$'s per-standardized-genotype effect in population $p$. Multiplying the two populations' expressions, taking expectations over the random effects, and using that sampling noise is independent across non-overlapping samples gives $\sqrt{N_1N_2}\sum_k r_{1jk}r_{2jk}\sigma_{1k}\sigma_{2k}\operatorname{Cov}(\beta_{1k},\beta_{2k})$; substituting the linear annotation model yields the regression. A category is enriched for trans-ethnic covariance when SNPs in strong LD with it (in both populations) have larger z-score products. Modelling per-allele rather than per-standardized-genotype effects lets allele-frequency differences between populations enter through $\sigma_{pk}$ instead of being confused with effect-size differences.

## Sources

- H. Shi, S. Gazal, M. Kanai, E. M. Koch, et al., "Population-specific causal disease effect sizes in functionally important regions impacted by selection", Nature Communications 12 (2021), Results (Equation (1)) and Methods, <https://doi.org/10.1038/s41467-021-21286-1> (PMC7889654).
