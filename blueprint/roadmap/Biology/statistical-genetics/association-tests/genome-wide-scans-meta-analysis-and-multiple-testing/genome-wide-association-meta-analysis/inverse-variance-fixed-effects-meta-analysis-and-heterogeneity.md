# Inverse-variance fixed-effects association test and the heterogeneity index

**Setting.** At one SNP $j$, studies $i = 1, \dots, N_j$ ($N_j \ge 2$) report strand-aligned allelic effect estimates $\beta_{ij}$ (log odds ratios for a binary trait), independent across studies, with known variances $V_{ij} = \operatorname{Var}(\beta_{ij}) > 0$; a study that does not report the SNP is left out. Under the fixed-effects model $\beta_{ij} \sim \mathcal{N}(\beta_j, V_{ij})$ with a common true effect $\beta_j$, let $\hat\beta_j = \sum_i \omega_{ij}\beta_{ij}$ be the average of the estimates with the [inverse-variance weights](../../../../../Probability/hypothesis-testing/meta-analysis/inverse-variance-weights.md) $\omega_{ij} = V_{ij}^{-1}/\sum_{i'} V_{i'j}^{-1}$, and let $Q_j$ be [Cochran's heterogeneity statistic](../../../../../Probability/hypothesis-testing/meta-analysis/cochran-q.md) of the $\beta_{ij}$ with variances $V_{ij}$.

**Association test.** The statistic

$$T_j = \hat\beta_j^2 \sum_i V_{ij}^{-1}$$

has exactly the $\chi^2_1$ law under $\beta_j = 0$ (approximately, when the $V_{ij}$ are estimated), and is the meta-analysis association test of $\beta_j = 0$.

**Heterogeneity index.** The index

$$I_j^2 = \max\!\left(0, \frac{Q_j - (N_j - 1)}{Q_j}\right) \qquad (Q_j > 0),$$

is the share of the variability of the estimates attributed to between-study heterogeneity rather than sampling error.

## Proof sketch

By [Cochran's minimum-variance theorem](../../../../../Probability/hypothesis-testing/meta-analysis/variance-inverse-variance-le.md), $\operatorname{Var}(\hat\beta_j) = (\sum_i V_{ij}^{-1})^{-1}$, and $\hat\beta_j$ is a linear combination of independent Gaussians with mean $\beta_j$; so under $\beta_j = 0$, $\hat\beta_j (\sum_i V_{ij}^{-1})^{1/2}$ is standard normal and $T_j \sim \chi^2_1$. Under homogeneity [Cochran's Q is $\chi^2_{N_j - 1}$](../../../../../Probability/hypothesis-testing/meta-analysis/has-law-cochran-q.md), so $\mathbb{E}Q_j = N_j - 1$; $I^2$ therefore measures excess dispersion on a scale that does not grow with the number of studies, unlike the $p$-value of $Q$. In genome-wide meta-analysis software the per-study directions of effect are also reported to flag inconsistent signals.

## Depends on

- [Inverse-variance weights](../../../../../Probability/hypothesis-testing/meta-analysis/inverse-variance-weights.md)
- [Cochran's heterogeneity statistic Q](../../../../../Probability/hypothesis-testing/meta-analysis/cochran-q.md)

## Proof depends on

- [Cochran's minimum-variance theorem for weighted averages](../../../../../Probability/hypothesis-testing/meta-analysis/variance-inverse-variance-le.md)

## Informally uses

- [Cochran's Q is chi-square under homogeneity](../../../../../Probability/hypothesis-testing/meta-analysis/has-law-cochran-q.md)

## Sources

- R. Mägi and A. P. Morris, "GWAMA: software for genome-wide association meta-analysis", BMC Bioinformatics 11 (2010), 288, Implementation ("Fixed-effects meta-analysis" and "Testing for heterogeneity between studies"), <https://doi.org/10.1186/1471-2105-11-288>, PMCID PMC2893603.
- J. P. T. Higgins and S. G. Thompson, "Quantifying heterogeneity in a meta-analysis", Statistics in Medicine 21 (2002), 1539–1558, <https://doi.org/10.1002/sim.1186>.
