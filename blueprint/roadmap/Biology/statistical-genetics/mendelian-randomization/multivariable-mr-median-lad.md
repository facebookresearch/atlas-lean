# MVMR-Median: least absolute deviations Mendelian randomization

In the summary-data model of [multivariable Mendelian randomization](multivariable-mr-ivw-and-egger.md), the MVMR-Median estimator is the weighted least absolute deviations fit

$$\hat\theta_{\mathrm{Med}} = \arg\min_{\theta \in \mathbb{R}^K}\sum_{j=1}^{p}\frac{1}{\sigma_{Yj}^2}\Big|\hat\beta_{Yj} - \sum_{k=1}^{K}\hat\beta_{Xjk}\theta_k\Big|,$$

a weighted median (50th percentile) regression, computed by quantile-regression algorithms. Since the $\hat\beta$ are continuous, the minimizer is unique with probability one. Standard errors are obtained by a parametric bootstrap that redraws $\hat\beta_{Yj} \sim N(\hat\beta_{Yj}, \sigma_{Yj}^2)$ and $(\hat\beta_{Xj1}, \dots, \hat\beta_{XjK}) \sim N\big(\hat\beta_{Xj}, \operatorname{diag}(\sigma_{Xj1}^2, \dots, \sigma_{XjK}^2)\big)$.

**Reduction for one risk factor.** For $K = 1$, with all $\hat\beta_{Xj1} \ne 0$,

$$\sum_{j=1}^{p}\frac{1}{\sigma_{Yj}^2}\big|\hat\beta_{Yj} - \hat\beta_{Xj1}\theta\big| = \sum_{j=1}^{p}\frac{|\hat\beta_{Xj1}|}{\sigma_{Yj}^2}\left|\frac{\hat\beta_{Yj}}{\hat\beta_{Xj1}} - \theta\right|,$$

so $\hat\theta_{\mathrm{Med}}$ is a weighted median of the ratio estimates $\hat\beta_{Yj}/\hat\beta_{Xj1}$ with weights proportional to $|\hat\beta_{Xj1}|/\sigma_{Yj}^2$ (the weighted empirical distribution median, rather than the interpolated version). The method extends median-based robustness to outlying and directionally pleiotropic variants to the multivariable setting.

## Depends on

- [Multivariable inverse-variance weighted and MR-Egger estimators](multivariable-mr-ivw-and-egger.md)
- [Ratio estimate of a single SNP](ratio-estimate.md)

## Expansion

A weighted sum $\sum_j w_j|r_j - \theta|$ is convex and piecewise linear in $\theta$, with slope $\sum_{r_j < \theta}w_j - \sum_{r_j > \theta}w_j$; it is minimized where the cumulative weight crosses half the total, i.e. at a weighted median of the $r_j$. Factoring $|\hat\beta_{Xj1}|$ out of each absolute residual turns the regression into exactly this problem for $r_j = \hat\beta_{Yj}/\hat\beta_{Xj1}$. Unlike robust MM-regression, least absolute deviations is not robust to influential points in the regressors, but it tolerates asymmetric distributions of pleiotropic effects.

## Sources

- A. J. Grant and S. Burgess, "Pleiotropy robust methods for multivariable Mendelian randomization", Statistics in Medicine 40 (2021), section 3.2, "Median based estimation", Equation (6), <https://doi.org/10.1002/sim.9156> (PMC7612169).
