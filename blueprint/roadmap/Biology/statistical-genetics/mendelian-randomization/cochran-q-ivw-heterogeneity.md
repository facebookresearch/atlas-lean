# Cochran's Q heterogeneity statistic for the IVW estimator

Let $J \ge 2$ SNPs have SNP–exposure associations $\hat\beta_{Xj} \ne 0$ and SNP–outcome associations $\hat\beta_{Yj}$ with standard errors $\sigma_{Yj} > 0$. Let $\hat\beta_j = \hat\beta_{Yj}/\hat\beta_{Xj}$ be the [ratio estimates](ratio-estimate.md), $w_j = \hat\beta_{Xj}^2/\sigma_{Yj}^2$ the first-order [inverse-variance weights](ivw-weight.md), and $\hat\beta_{\mathrm{IVW}} = \sum_j w_j \hat\beta_j / \sum_j w_j$ the [IVW estimator](ivw.md). The IVW heterogeneity statistic is [Cochran's Q](../../../Probability/hypothesis-testing/meta-analysis/cochran-q.md) of the estimates $\hat\beta_j$ with variances $v_j = 1/w_j$, which in Mendelian-randomization notation reads

$$Q = \sum_{j=1}^{J} w_j \left( \hat\beta_j - \hat\beta_{\mathrm{IVW}} \right)^2 = \sum_{j=1}^{J} \frac{\left(\hat\beta_{Yj} - \hat\beta_{\mathrm{IVW}}\, \hat\beta_{Xj}\right)^2}{\sigma_{Yj}^2}.$$

If the $\hat\beta_{Yj}$ are independent with $\hat\beta_{Yj} \sim N(\beta \hat\beta_{Xj}, \sigma_{Yj}^2)$ for a common causal effect $\beta$, treating $\hat\beta_{Xj}$ and $\sigma_{Yj}$ as fixed (no measurement error in the exposure associations, the "NOME" assumption), then $Q \sim \chi^2_{J-1}$ exactly. An excess of $Q$ over $J - 1$ indicates heterogeneity of the ratio estimates, which Bowden et al. interpret as evidence of pleiotropy (invalid instruments).

## Depends on

- [Ratio estimate of a single SNP](ratio-estimate.md)
- [Inverse-variance weight of a ratio estimate](ivw-weight.md)
- [Inverse-variance-weighted estimator](ivw.md)
- [Cochran's heterogeneity statistic Q](../../../Probability/hypothesis-testing/meta-analysis/cochran-q.md)

## Proof depends on

- [Cochran's Q is chi-square under homogeneity](../../../Probability/hypothesis-testing/meta-analysis/has-law-cochran-q.md)

## Expansion

With $v_j = 1/w_j$ the normalized inverse-variance weights are $w_j / \sum_k w_k$, so their weighted mean of the $\hat\beta_j$ is $\hat\beta_{\mathrm{IVW}}$ and $v_j^{-1}(\hat\beta_j - \hat\beta_{\mathrm{IVW}})^2 = w_j(\hat\beta_j - \hat\beta_{\mathrm{IVW}})^2$; the second form follows from $w_j(\hat\beta_j - b)^2 = (\hat\beta_{Yj} - b\hat\beta_{Xj})^2/\sigma_{Yj}^2$. Under the stated model the $\hat\beta_j$ are independent with $\hat\beta_j \sim N(\beta, \sigma_{Yj}^2/\hat\beta_{Xj}^2) = N(\beta, v_j)$, so the chi-square law of Cochran's Q under homogeneity gives $Q \sim \chi^2_{J-1}$. The second form also shows that $Q$ is the minimized weighted residual sum of squares of the regression of $\hat\beta_{Yj}$ on $\hat\beta_{Xj}$ through the origin with weights $\sigma_{Yj}^{-2}$. Uncertainty in $\hat\beta_{Xj}$ makes first-order weights anti-conservative; Bowden et al. also consider second-order weights.

## Sources

- J. Bowden, F. Del Greco M, C. Minelli, G. Davey Smith, N. Sheehan and J. Thompson, *A framework for the investigation of pleiotropy in two-sample summary data Mendelian randomization*, Stat. Med. 36 (2017), 1783–1802. <https://doi.org/10.1002/sim.7221>, PMCID: PMC5434863.
