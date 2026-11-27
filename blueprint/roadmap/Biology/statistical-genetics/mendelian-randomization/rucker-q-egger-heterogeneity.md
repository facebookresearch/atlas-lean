# Rücker's Q′ for MR-Egger and the Q − Q′ comparison

In the setting of [Cochran's Q for the IVW estimator](cochran-q-ivw-heterogeneity.md), orient each SNP so that $\hat\beta_{Xj} > 0$ and let $(\hat\beta_{0E}, \hat\beta_{1E})$ be the MR-Egger intercept and slope, the weighted least-squares fit of $\hat\beta_{Yj}$ on $\hat\beta_{Xj}$ with an intercept and weights $\sigma_{Yj}^{-2}$ ([MR-Egger slope](egger-slope.md), [MR-Egger intercept](egger-intercept.md)). Rücker's statistic is the residual sum of squares of that fit,

$$Q' = \sum_{j=1}^{J} \frac{\left(\hat\beta_{Yj} - \hat\beta_{0E} - \hat\beta_{1E}\hat\beta_{Xj}\right)^2}{\sigma_{Yj}^2}.$$

Under independent Gaussian outcome associations $\hat\beta_{Yj} \sim N(\beta_0 + \beta_1\hat\beta_{Xj}, \sigma_{Yj}^2)$ with fixed $\hat\beta_{Xj}$, $\sigma_{Yj}$ and $J \ge 3$ not all $\hat\beta_{Xj}$ equal, $Q' \sim \chi^2_{J-2}$. If moreover $\beta_0 = 0$ (no directional pleiotropy), the IVW model is nested in the Egger model and

$$Q - Q' \sim \chi^2_1, \quad \text{independent of } Q'.$$

A large $Q - Q'$ says that the Egger intercept removes a significant share of the heterogeneity, i.e. evidence of directional pleiotropy; a large $Q'$ says heterogeneity remains after allowing for it.

## Depends on

- [Cochran's Q heterogeneity statistic for the IVW estimator](cochran-q-ivw-heterogeneity.md)
- [MR-Egger slope](egger-slope.md)
- [MR-Egger intercept](egger-intercept.md)
- [MR-Egger line is the weighted least-squares line](egger-ssr-le.md)

## Expansion

After standardizing by $\sigma_{Yj}$ both fits are ordinary least squares in nested linear models with $1$ and $2$ coefficients. Cochran's theorem gives $\chi^2$ laws with $J - 1$ and $J - 2$ degrees of freedom for the residual sums of squares, and their difference is the squared length of the projection onto the one extra direction, which is $\chi^2_1$ and orthogonal to the Egger residual when the extra coefficient is zero. Orienting SNPs to positive $\hat\beta_{Xj}$ makes the intercept interpretable as average directional pleiotropy and makes the test invariant to allele coding.

## Sources

- J. Bowden, F. Del Greco M, C. Minelli, G. Davey Smith, N. Sheehan and J. Thompson, *A framework for the investigation of pleiotropy in two-sample summary data Mendelian randomization*, Stat. Med. 36 (2017), 1783–1802. <https://doi.org/10.1002/sim.7221>, PMCID: PMC5434863.
