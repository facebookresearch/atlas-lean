# Inverse-variance fixed-effects meta-analysis and heterogeneity statistics

**Setting.** At one SNP $j$, studies $i = 1, \dots, N_j$ report strand-aligned allelic effect estimates $\beta_{ij}$ (log odds ratios for a binary trait) with known variances $V_{ij} = \operatorname{Var}(\beta_{ij}) > 0$, independent across studies. Put $w_{ij} = V_{ij}^{-1}$ (and $w_{ij} = 0$ for a study that does not report the SNP).

**Fixed-effects estimator.** Under the fixed-effects model $\beta_{ij} \sim \mathcal{N}(\beta_j, V_{ij})$ with a common true effect $\beta_j$,

$$\hat\beta_j = \frac{\sum_i w_{ij}\beta_{ij}}{\sum_i w_{ij}}, \qquad \operatorname{Var}(\hat\beta_j) = \frac{1}{\sum_i w_{ij}},$$

and $\hat\beta_j$ is the maximum-likelihood and minimum-variance unbiased linear estimator of $\beta_j$. The statistic $\hat\beta_j^2 \sum_i w_{ij}$ is exactly $\chi^2_1$ under $\beta_j = 0$ (approximately, when the $V_{ij}$ are estimated) and is the meta-analysis association test.

**Heterogeneity.** Cochran's statistic

$$Q_j = \sum_i w_{ij}\big(\beta_{ij} - \hat\beta_j\big)^2$$

is $\chi^2_{N_j - 1}$ under the fixed-effects model, and

$$I_j^2 = \max\!\left(0, \frac{Q_j - (N_j - 1)}{Q_j}\right)$$

is the share of the variability of the estimates attributed to between-study heterogeneity rather than sampling error.

## Expansion

The weighted mean minimizes $\sum_i w_{ij}(\beta_{ij} - b)^2$ over $b$, and its variance follows from independence: $\operatorname{Var}(\sum_i w_{ij}\beta_{ij}) = \sum_i w_{ij}$. Under the model the standardized residuals $\sqrt{w_{ij}}(\beta_{ij} - \beta_j)$ are i.i.d. standard normal, and $Q_j$ is their sum of squares after projecting out the one-dimensional direction $(\sqrt{w_{1j}}, \dots)$, which removes one degree of freedom. Because $\mathbb{E}Q_j = N_j - 1$ under homogeneity, $I^2$ measures excess dispersion on a scale that does not grow with the number of studies, unlike the $p$-value of $Q$. In genome-wide meta-analysis software the per-study directions of effect are also reported to flag inconsistent signals.

## Sources

- R. Mägi and A. P. Morris, "GWAMA: software for genome-wide association meta-analysis", BMC Bioinformatics 11 (2010), 288, Implementation ("Fixed-effects meta-analysis" and "Testing for heterogeneity between studies"), <https://doi.org/10.1186/1471-2105-11-288>, PMCID PMC2893603.
- J. P. T. Higgins and S. G. Thompson, "Quantifying heterogeneity in a meta-analysis", Statistics in Medicine 21 (2002), 1539–1558, <https://doi.org/10.1002/sim.1186>.
