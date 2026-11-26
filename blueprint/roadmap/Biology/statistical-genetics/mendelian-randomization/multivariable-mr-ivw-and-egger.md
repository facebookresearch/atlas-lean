# Multivariable inverse-variance weighted and MR-Egger estimators

Consider $p$ independent genetic variants, $K < p$ risk factors and one outcome. From summary data let $\hat\beta_{Xjk}$ be the estimated association of variant $j$ with risk factor $k$ and $\hat\beta_{Yj}$ its association with the outcome, with

$$\hat\beta_{Xjk} = \beta_{Xjk} + \varepsilon_{Xjk}, \qquad \hat\beta_{Yj} = \alpha_j + \sum_{k=1}^{K}\beta_{Xjk}\theta_k + \varepsilon_{Yj},$$

where $\theta = (\theta_1, \dots, \theta_K)$ are the direct causal effects of the risk factors on the outcome, $\alpha_j$ is the pleiotropic effect of variant $j$ not mediated by the measured risk factors ($\alpha_j = 0$ for a valid instrument), and $\operatorname{Var}(\varepsilon_{Yj}) = \sigma_{Yj}^2$ is treated as known. The $p \times K$ matrix $(\beta_{Xjk})$ is assumed to have full column rank.

**MVMR-IVW.** The multivariable inverse-variance weighted estimator is the weighted least-squares fit without intercept,

$$\hat\theta_{\mathrm{IVW}} = \arg\min_{\theta}\sum_{j=1}^{p}\frac{1}{\sigma_{Yj}^2}\Big(\hat\beta_{Yj} - \sum_{k=1}^{K}\hat\beta_{Xjk}\theta_k\Big)^2 = (B^\top WB)^{-1}B^\top W\hat\beta_Y,$$

with $B = (\hat\beta_{Xjk})$ and $W = \operatorname{diag}(\sigma_{Yj}^{-2})$. It is consistent when all variants are valid, and remains consistent when pleiotropy is balanced (mean-zero $\alpha_j$) and satisfies InSIDE, the independence of the $\alpha_j$ from the variant–risk-factor associations.

**MVMR-Egger.** Adding an intercept,

$$(\hat\theta_0, \hat\theta_{\mathrm{Egger}}) = \arg\min_{\theta_0, \theta}\sum_{j=1}^{p}\frac{1}{\sigma_{Yj}^2}\Big(\hat\beta_{Yj} - \theta_0 - \sum_{k=1}^{K}\hat\beta_{Xjk}\theta_k\Big)^2,$$

absorbs directional (nonzero-mean) pleiotropy and gives a consistent estimator under InSIDE even when every variant is invalid, at the cost of precision.

**Orientation.** Recoding variant $j$ with the other allele as effect allele multiplies $\hat\beta_{Yj}$ and all $\hat\beta_{Xjk}$ by $-1$. The IVW objective, and hence $\hat\theta_{\mathrm{IVW}}$, is invariant under such recodings; the Egger objective is not, because the intercept does not change sign, so MVMR-Egger depends on the chosen orientation (conventionally, positive associations with a primary risk factor).

## Depends on

- [Inverse-variance weighted estimator](ivw.md)
- [MR-Egger slope](egger-slope.md)
- [MR-Egger intercept](egger-intercept.md)

## Expansion

For $K = 1$ the two estimators reduce to the univariable [IVW](ivw.md) and [MR-Egger](egger-slope.md) estimators. Under the model, $\mathbb{E}[\hat\beta_{Yj} \mid \beta_X] = \alpha_j + \beta_{Xj}^\top\theta$, so the IVW fit is a regression through the origin whose residuals contain $\alpha_j$; its limit is $\theta$ exactly when the weighted average of $\alpha_j\beta_{Xj}$ vanishes, which is what balance plus InSIDE provide. With an intercept, a common nonzero mean of the $\alpha_j$ is fitted by $\theta_0$ instead of biasing $\theta$. Under recoding, the $j$th IVW residual flips sign, leaving its square unchanged, while the Egger residual becomes $-(\hat\beta_{Yj} + \theta_0 - \hat\beta_{Xj}^\top\theta)$.

## Sources

- A. J. Grant and S. Burgess, "Pleiotropy robust methods for multivariable Mendelian randomization", Statistics in Medicine 40 (2021), sections 2.4–2.6 and 3.1, Equations (4)–(5), <https://doi.org/10.1002/sim.9156> (PMC7612169).
