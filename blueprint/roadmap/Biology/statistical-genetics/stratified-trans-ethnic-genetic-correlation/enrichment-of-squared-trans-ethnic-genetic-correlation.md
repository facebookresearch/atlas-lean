# Enrichment of squared trans-ethnic genetic correlation

With the annotation-level trans-ethnic genetic covariance $\rho_g(C)$ and population-specific heritabilities $h^2_{g1}(C), h^2_{g2}(C)$ from [trans-ethnic LD score regression](trans-ethnic-ld-score-regression-of-z-score-products.md), define the stratified squared trans-ethnic genetic correlation of a category $C$

$$r_g^2(C) = \frac{\rho_g(C)^2}{h^2_{g1}(C)\,h^2_{g2}(C)},$$

and its enrichment relative to the genome-wide value $r_g^2$,

$$\lambda^2(C) = \frac{r_g^2(C)}{r_g^2} .$$

$\lambda^2(C) < 1$ means causal effect sizes in $C$ are more population-specific than average, $\lambda^2(C) > 1$ more shared. Because $\lambda^2(C)$ is a ratio to the trait's own $r_g^2$, it can be meta-analysed across traits with different genome-wide correlations. Estimates use an analytical bias correction and a shrinkage parameter ($\alpha = 0.5$ by default) to stabilize noisy annotation-level heritabilities, with block-jackknife standard errors. Across 31 traits in East Asian and European samples (average $r_g = 0.85$), $\lambda^2(C)$ was below 1 in the top quintile of the background-selection statistic and in most functional annotations, and below 1 for all 53 tissue-specific expressed-gene annotations, with the strongest depletion in skin, prostate and ovary.

## Depends on

- [Trans-ethnic LD score regression of z-score products](trans-ethnic-ld-score-regression-of-z-score-products.md)

## Expansion

Stratifying the squared correlation, rather than the correlation itself, avoids taking square roots of small and noisy heritability estimates and keeps the ratio defined when a heritability estimate is near zero after shrinkage. A depletion in regions under strong background selection is what one expects if purifying or population-specific selection makes causal effects in those regions differ more between populations, or if gene-by-environment interaction is concentrated in genes expressed in environment-facing tissues.

## Sources

- H. Shi, S. Gazal, M. Kanai, E. M. Koch, et al., "Population-specific causal disease effect sizes in functionally important regions impacted by selection", Nature Communications 12 (2021), Results (Equation (2), definition of $\lambda^2(C)$, applications) and Methods, <https://doi.org/10.1038/s41467-021-21286-1> (PMC7889654).
