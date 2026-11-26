# Semi-supervised estimation of explained variance and $R^2$ in high dimensions

Use the setting and cross-fitting folds of the [cross-fitted semi-supervised mean estimator](cross-fitted-semi-supervised-mean-estimator.md): $\tilde X = (1, X^\top)^\top$, $\beta^*$ the $\ell_2$ projection coefficient, $\varepsilon = Y - \tilde X^\top\beta^*$, $\sigma_Y^2 = \operatorname{var}(Y)$, $b^2 = \operatorname{var}(\tilde X^\top\beta^*)$, $\tau = \lim n/(m+n)$, and the proportion of variance explained $\mathrm{PVE} = b^2/\sigma_Y^2$. Let $\tilde V = \tilde X - E\tilde X$. In fold $k$ put $\hat V_i = \tilde X_i - \hat\mu^{(k)}$, $\hat C^{(k)} = M^{-1}\sum_{i\in J_k}\hat V_i\hat V_i^\top$ and $\hat\varepsilon_i = Y_i - \hat\theta - \hat\beta^{(-k)\top}\hat V_i$, and define

$$\hat b^{2(k)} = \hat\beta^{(-k)\top}\hat C^{(k)}\hat\beta^{(-k)} + 2N^{-1}\sum_{i\in I_k}\hat\beta^{(-k)\top}\hat V_i\hat\varepsilon_i,$$

$$\hat\sigma_Y^{2(k)} = N^{-1}\sum_{i\in I_k}(Y_i - \hat\theta)^2 + N^{-1}\sum_{i\in I_k}\hat\beta^{(-k)\top}\big(\hat C^{(k)} - \hat V_i\hat V_i^\top\big)\hat\beta^{(-k)},$$

with $\hat\sigma_Y^2 = K^{-1}\sum_k \hat\sigma_Y^{2(k)}$ and $R^2 = K^{-1}\sum_k \hat b^{2(k)}/\hat\sigma_Y^{2(k)}$.

**Conditions.** (C1) as for the mean estimator; (C2) $E|Y|^{4+c} < c_1$, $\lambda_{\min}(C) > 0$, $\lambda_{\max}(C) \le c_1$ and $\sup_{\|a\|_2=1}E|a^\top Z|^{4+c} < c_1$; (C4) $\|\hat\beta - \beta^*\|_2 = o_P(1)$.

**Theorem 4 (Zhang and Bradic).** Under (C2) and (C4), as $m, n, p \to \infty$,

$$n^{1/2}(\hat\sigma_Y^2 - \sigma_Y^2) \to N\big(0,\ \operatorname{var}(\varepsilon^2 + 2\beta^{*\top}\tilde V\varepsilon) + \tau\operatorname{var}\{(\beta^{*\top}\tilde V)^2\}\big)$$

in distribution, provided the variance exceeds some $c > 0$; a consistent estimator of that variance exists.

**Corollary 1 (Zhang and Bradic).** Under (C1) and (C4), $R^2 = \mathrm{PVE} + o_P(1)$. If (C2) holds and $\|\hat\beta - \beta^*\|_2 = o_P(n^{-1/4})$, then $n^{1/2}V(R^2)^{-1/2}(R^2 - \mathrm{PVE}) \to N(0,1)$ whenever $V(R^2) > 0$, where

$$V(R^2) = \operatorname{var}\big[\sigma_Y^{-4}b^2\varepsilon^2 + \sigma_Y^{-4}\sigma_\varepsilon^2\{2\varepsilon\beta^{*\top}\tilde V + \tau(\beta^{*\top}\tilde V)^2\}\big] + \tau\sigma_Y^{-8}\sigma_\varepsilon^4\operatorname{var}\{(\beta^{*\top}\tilde V)^2\}.$$

## Depends on

- [Cross-fitted semi-supervised estimator of a mean in high dimensions](cross-fitted-semi-supervised-mean-estimator.md)

## Expansion

The naive residual mean square inflates the variance: $n^{-1}\sum_i(Y_i - \hat\theta)^2 = \sigma_Y^2 + n^{-1}\sum_i \beta^{*\top}(\tilde V_i\tilde V_i^\top - \tilde C)\beta^* + T + O_P(n^{-1})$ with $E T = 0$. The second sum in $\hat\sigma_Y^{2(k)}$ is a cross-fitted estimate of minus the middle term, built from the pooled covariance $\hat C^{(k)}$, so adding it cancels that term. Similarly, the cross term in $\hat b^{2(k)}$ corrects the plug-in quadratic form, so $\hat b^2 - b^2 = O_P(\|\hat\beta-\beta^*\|_2^2 + n^{-1/2})$ under (C2), against $O_P(\|\hat\beta-\beta^*\|_2)$ for the plug-in. The corollary is the delta method applied to the ratio.

## Sources

- Y. Zhang and J. Bradic, *High-dimensional semi-supervised learning: in search of optimal inference of the mean*, Biometrika (2022). <https://doi.org/10.1093/biomet/asab042>. Section 2.2, equations (2)–(4); Section 2.4, Theorem 4 and Corollary 1.
