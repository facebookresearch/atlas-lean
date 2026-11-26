# Stratification inflation scales linearly with sample size

**Setting.** Work in the LD-score model with constant stratification: $N$ individuals, $M$ markers, SNP heritability $h^2$, and a stratification term $a = s^2\bigl(\tfrac1N\sum_i X_{ij} c_i\bigr)^2$, the same for every marker $j$ (the squared covariance of the standardized genotypes with the stratification axis $c$, scaled by its effect $s$), so that the [mean expected association statistic](../../ld-score-regression/mean-integral-chi-sq-strat-of-const.md) is

$$\lambda(N) = \frac{1}{M}\sum_{j=1}^{M} \mathbb{E}\chi^2_j = 1 - h^2 + N\Bigl(\frac{h^2}{M}\bar\ell + a\Bigr),$$

with $\bar\ell$ the mean LD score. This is the population [genomic-control factor](lambda-gc.md).

**Proposition.** If the per-individual quantities $h^2$, $\bar\ell/M$ and $a$ do not depend on the sample size, then for any two sample sizes $N_1, N_2 > 0$

$$\lambda(N_2) - (1 - h^2) = \frac{N_2}{N_1}\bigl(\lambda(N_1) - (1 - h^2)\bigr).$$

In particular, for a trait with no heritability at the markers ($h^2 = 0$), such as a GWAS of birthplace coordinates that measures pure stratification,

$$\lambda(N_2) = \frac{N_2}{N_1}\bigl(\lambda(N_1) - 1\bigr) + 1.$$

## Proof sketch

Both the polygenic signal and the stratification bias enter the expected $\chi^2$ through terms proportional to $N$, because each is a squared mean shift whose estimate sharpens with sample size, while the null contribution $1 - h^2$ does not grow. Subtracting the constant and taking the ratio at two sample sizes gives the proposition. The rescaling is used to calibrate simulations to a biobank: an inflation $\lambda \approx 12$ on birthplace coordinates in a sample of $300{,}000$ corresponds to $\lambda \approx (9{,}000/300{,}000)(12 - 1) + 1 = 1.33$ in a simulated sample of $9{,}000$, which fixes the migration rate of the simulated spatial population. The same linearity explains why stratification that is invisible in small samples becomes the dominant inflation in very large ones, and why residual stratification in effect sizes propagates into polygenic scores even after standard corrections.

## Depends on

- [Mean association statistic with constant stratification](../../ld-score-regression/mean-integral-chi-sq-strat-of-const.md)
- [Population genomic-control factor of the LD-score model](lambda-gc.md)

## Sources

- A. A. Zaidi and I. Mathieson, "Demographic history mediates the effect of stratification on polygenic scores", eLife 9 (2020), e61548, <https://doi.org/10.7554/eLife.61548>, PMCID PMC7758063. Materials and methods, Equation 1 and the choice of migration rates.
- B. K. Bulik-Sullivan, P.-R. Loh, H. K. Finucane et al., "LD Score regression distinguishes confounding from polygenicity in genome-wide association studies", Nature Genetics 47 (2015), 291–295, <https://doi.org/10.1038/ng.3211>.
