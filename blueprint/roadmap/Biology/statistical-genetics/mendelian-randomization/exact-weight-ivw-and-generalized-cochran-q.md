# Exact-weight IVW estimator and the generalized Cochran's Q beyond the NOME assumption

Let $L \ge 2$ uncorrelated SNPs have true SNP–exposure associations $\gamma_j \ne 0$, exposure estimates $\hat\gamma_j$ with standard errors $\sigma_{Xj} > 0$, and outcome estimates $\hat\Gamma_j$ with standard errors $\sigma_{Yj} > 0$, the two sets of estimates coming from independent samples. Assume no pleiotropy and a common causal effect $\beta$:

$$\hat\Gamma_j = \beta\gamma_j + \sigma_{Yj}\epsilon_j, \qquad \hat\gamma_j = \gamma_j + \sigma_{Xj}\eta_j, \qquad \epsilon_j, \eta_j \overset{\text{iid}}{\sim} N(0,1).$$

With ratio estimates $\hat\beta_j = \hat\Gamma_j / \hat\gamma_j$ define the $\beta$-dependent weights and the generalized Q statistic

$$w_j(\beta) = \frac{\hat\gamma_j^2}{\sigma_{Yj}^2 + \beta^2\sigma_{Xj}^2}, \qquad Q_m(\beta) = \sum_{j=1}^{L} w_j(\beta)\,(\hat\beta_j - \beta)^2 = \sum_{j=1}^{L} \frac{(\hat\Gamma_j - \beta\hat\gamma_j)^2}{\sigma_{Yj}^2 + \beta^2\sigma_{Xj}^2}.$$

**Special cases.** First-order weights are $w_j(0) = \hat\gamma_j^2/\sigma_{Yj}^2$ (the NOME, "no measurement error", assumption), second-order weights are $w_j(\hat\beta_j)$, and the iterative estimator plugs $w_j(\hat\beta^{(i-1)})$ into the IVW formula $\sum_j w_j\hat\beta_j / \sum_j w_j$ starting from the first-order estimate.

**Definition (exact IVW estimate).** $\hat\beta_{\mathrm{exact}} = \arg\min_\beta Q_m(\beta)$, with the weights varying with $\beta$ during the minimization; its heterogeneity statistic is $Q_m(\hat\beta_{\mathrm{exact}})$.

**Proposition.** Under the model above, at the true $\beta$ the terms $(\hat\Gamma_j - \beta\hat\gamma_j)/\sqrt{\sigma_{Yj}^2 + \beta^2\sigma_{Xj}^2}$ are independent standard normal, so $Q_m(\beta) \sim \chi^2_L$ exactly, whatever the instrument strengths $\gamma_j/\sigma_{Xj}$. Consequently $\{\beta : Q_m(\beta) \le q\}$ with $q$ a $\chi^2$ quantile is a confidence set obtained by inverting $Q_m$; the paper uses the $\chi^2_{L-1}$ quantile at the exact estimate.

## Depends on

- [Ratio estimate of a single SNP](ratio-estimate.md)
- [Inverse-variance-weighted estimator](ivw.md)
## Expansion

$\hat\Gamma_j - \beta\hat\gamma_j = \sigma_{Yj}\epsilon_j - \beta\sigma_{Xj}\eta_j$ is a sum of independent centred normals with variance $\sigma_{Yj}^2 + \beta^2\sigma_{Xj}^2$, which gives the proposition, and $w_j(\beta)(\hat\beta_j-\beta)^2$ equals the displayed squared standardized residual because $\hat\gamma_j^2(\hat\Gamma_j/\hat\gamma_j - \beta)^2 = (\hat\Gamma_j - \beta\hat\gamma_j)^2$. Replacing $\gamma_j$ by $\hat\gamma_j$ in the outcome model inflates the residual variance by $\beta^2\sigma_{Xj}^2$; first-order weights ignore this, so with weak instruments and $\beta \ne 0$ Cochran's Q is anti-conservative, while second-order weights evaluated at the noisy $\hat\beta_j$ over-inflate the variance and lose power. Minimizing $Q_m$ with $\beta$-dependent weights is the two-sample summary-data analogue of limited-information maximum likelihood and removes regression-dilution bias of the IVW estimate; under the causal null $\beta = 0$ all weightings coincide with first order.

## Sources

- J. Bowden, F. Del Greco M, C. Minelli, Q. Zhao, D. A. Lawlor, N. A. Sheehan, J. Thompson and G. Davey Smith, "Improving the accuracy of two-sample summary-data Mendelian randomization: moving beyond the NOME assumption", International Journal of Epidemiology 48 (2019), 728–742, Box 1, Box 2 (Equations 2–6) and Box 3 (Equations 7–10), <https://doi.org/10.1093/ije/dyy258> (PMC6659376).
