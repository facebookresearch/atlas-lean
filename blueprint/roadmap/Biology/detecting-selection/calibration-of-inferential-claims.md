# Calibration of inferential claims in population genetics

Tests and intervals in population genetics are calibrated in three distinct ways. Exact calibration uses finite-model tail probabilities: the Ewens–Watterson test refers the sample homozygosity to its conditional law given the number of alleles, which does not depend on the mutation parameter, and Watterson (1978, Abstract) tabulates significance points and moments of the homozygosity under neutrality. Approximate calibration standardizes a statistic: Achaz (2009, Equation 1 and the following text) writes neutrality tests as a difference of two estimators of $\theta$ divided by its standard deviation, which requires the difference to have positive variance; then $E[T] = 0$ and $\mathrm{Var}[T] = 1$ for known $\theta$ under the standard model; because the variance involves $\theta$ and $\theta^2$, these are replaced by estimators based on the number of segregating sites, after which only $E[T] \approx 0$ and $\mathrm{Var}[T] \approx 1$ hold. Empirical calibration uses simulation, as for the [Poisson likelihood of the joint site-frequency spectrum](../population-genetics/diffusion-theory/poisson-random-field-model/expected-joint-allele-frequency-spectrum-and-poisson-likelihood.md), which is a composite likelihood under linkage, so that its variances and critical values come from simulations incorporating linkage (Gutenkunst, Hernandez, Williamson and Bustamante 2009, Methods).

## Depends on

- [Expected joint allele-frequency spectrum and its Poisson likelihood](../population-genetics/diffusion-theory/poisson-random-field-model/expected-joint-allele-frequency-spectrum-and-poisson-likelihood.md)
- [Conditional upper-tail p-value of the Ewens–Watterson test](../../Biology/detecting-selection/ewens-watterson-test/cond-upper-pvalue.md)
- [Conditional validity of the Ewens–Watterson test](../../Biology/detecting-selection/ewens-watterson-test/sum-cond-upper-pvalue-le-cond.md)
- [Sufficient conditions for asymptotic normality of Tajima's D](../../Biology/detecting-selection/mean-and-asymptotic-normality-of-tajima-s-d/tendsto-in-distribution-tajima-d-gaussia.md)
- [Bounded Tajima statistics exclude nondegenerate Gaussian laws](../../Biology/detecting-selection/mean-and-asymptotic-normality-of-tajima-s-d/not-has-law-tajima-d-gaussian-real.md)

## Expansion

1. Exact conditional tests: the Ewens–Watterson test given the number of alleles, and the validity of its conditional p-value.
2. Standardized neutrality tests, for a contrast of positive variance: the exact moments for known $\theta$ and the approximation after plugging in estimates of $\theta$ and $\theta^2$.
3. Asymptotic calibration: conditions for normal limits of standardized statistics, and their failure for bounded statistics such as Tajima's $D$.
4. Simulation-based calibration of composite likelihoods under linkage, and its Monte Carlo error.

## Sources

- G. A. Watterson, The homozygosity test of neutrality, Genetics 88 (1978), 405–417, Abstract. <https://doi.org/10.1093/genetics/88.2.405>
- G. Achaz, Frequency spectrum neutrality tests: one for all and all for one, Genetics 183 (2009), 249–258, Equation 1 and the following text. <https://doi.org/10.1534/genetics.109.104042>
- R. N. Gutenkunst, R. D. Hernandez, S. H. Williamson and C. D. Bustamante, Inferring the joint demographic history of multiple populations from multidimensional SNP frequency data, PLoS Genet. 5 (2009), e1000695, Methods (Likelihood-based inference). <https://doi.org/10.1371/journal.pgen.1000695>
