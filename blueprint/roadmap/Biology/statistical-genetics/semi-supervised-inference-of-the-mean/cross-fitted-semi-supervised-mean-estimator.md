# Cross-fitted semi-supervised estimator of a mean in high dimensions

**Setting.** Observe $n$ i.i.d. labeled pairs $(X_i, Y_i)$, $i = 1, \dots, n$, with $X_i \in \mathbb{R}^{p-1}$ and $Y_i \in \mathbb{R}$, plus $m$ further covariate vectors $X_{n+1}, \dots, X_{n+m}$ from the same covariate law (outcomes missing completely at random), and let $\tau = \lim_{m,n\to\infty} n/(m+n) \in [0,1]$. Write $\tilde X = (1, X^\top)^\top$, $\mu = E X$, $C = \operatorname{cov}(X)$, $Z = C^{-1/2}(X-\mu)$, and let

$$\beta^* = \arg\min_{\beta \in \mathbb{R}^p} E(Y - \beta_1 - X^\top \beta_{-1})^2, \qquad \varepsilon = Y - \tilde X^\top \beta^*, \qquad \sigma_\varepsilon^2 = \operatorname{var}(\varepsilon), \qquad b^2 = \operatorname{var}(\tilde X^\top \beta^*).$$

No linear model for $E(Y \mid X)$ is assumed. The target is $\theta = E Y = E(\tilde X)^\top \beta^*$.

**Estimator.** Split the labeled indices into $K$ folds $I_k$ of size $N$ and the unlabeled indices into $I_k'$, with $J_k = I_k \cup I_k'$ of size $M$. Let $\hat\beta^{(-k)}$ be any estimate of $\beta^*$ (Lasso, square-root Lasso, ...) computed from labeled data outside $I_k$. Set

$$\hat\theta^{(k)} = \hat\mu^{(k)\top}\hat\beta^{(-k)} + N^{-1}\sum_{i \in I_k}\big(Y_i - \tilde X_i^\top \hat\beta^{(-k)}\big), \qquad \hat\mu^{(k)} = M^{-1}\sum_{i\in J_k}\tilde X_i, \qquad \hat\theta = K^{-1}\sum_{k=1}^K \hat\theta^{(k)}.$$

**Conditions.** (C1) $\lambda_{\min}(C) > 0$, $\lambda_{\max}(C) \le c_1$, $\sup_{\|a\|_2=1} E|a^\top Z|^{2+c} < c_1$ and $E|Y|^{2+c} < c_1$ for constants $c, c_1 > 0$. (C3) $\|\hat\beta - \beta^*\|_2 = O_P(1)$. (C4) $\|\hat\beta - \beta^*\|_2 = o_P(1)$.

**Theorem (Zhang and Bradic, Theorems 1–3).** As $m, n, p \to \infty$:

1. Under (C1) and (C3), $\hat\theta - \theta = O_P(n^{-1/2})$.
2. Under (C1) and (C4), if $\sigma_\varepsilon^2 + \tau b^2 > c$ for some $c > 0$, then

$$n^{1/2}(\hat\theta - \theta) \to N(0, \sigma_\varepsilon^2 + \tau b^2) \quad \text{in distribution.}$$

3. Under (C1) and (C4), with cross-fitted residuals $\hat\varepsilon_i$ and $\hat\sigma_\varepsilon^2 = n^{-1}\sum_{i=1}^n \hat\varepsilon_i^2$, one has $\hat\sigma_\varepsilon^2 \to \sigma_\varepsilon^2$ and $\hat b^2 \to b^2$ in probability, and

$$\hat\theta \pm z_{1-\alpha/2}\{\hat\sigma_\varepsilon^2/n + \hat b^2/(m+n)\}^{1/2}$$

is an asymptotically valid level-$(1-\alpha)$ confidence interval for $\theta$.

Since $\operatorname{var}(n^{1/2}\bar Y) = \sigma_Y^2 = \sigma_\varepsilon^2 + b^2$, the unlabeled data reduce the asymptotic variance by $(1-\tau)b^2$; with $\tau = 0$ the variance equals that attainable with the covariate law known. Only consistency of $\hat\beta$, at any rate, is needed for valid inference.

## Expansion

With the covariate law known, debiasing $\hat\beta$ with $\tilde\Sigma^{-1}$ collapses to $\bar Y + (E\tilde X - \bar{\tilde X})^\top\hat\beta$, the low-dimensional semi-supervised estimator. The error of its sample analogue splits as $t_1 + t_2 + t_3$ with $t_1 = \theta - \bar Y$, $t_2 = (\bar{\tilde X} - \hat\mu)^\top(\hat\beta - \beta^*)$ and $t_3 = (\bar{\tilde X} - \hat\mu)^\top\beta^*$. Cross-fitting makes $\hat\beta^{(-k)}$ independent of the fold that forms $t_2$, so $t_2 = o_P(n^{-1/2})$ conditionally on consistency alone, instead of the sparsity $s \le n^{1/2}/\log p$ an $\ell_1$-$\ell_\infty$ bound would need. The leading terms $t_1 + t_3$ give the variance $\sigma_\varepsilon^2 + \tau b^2$.

## Sources

- Y. Zhang and J. Bradic, *High-dimensional semi-supervised learning: in search of optimal inference of the mean*, Biometrika (2022). <https://doi.org/10.1093/biomet/asab042>. Sections 2.1, 2.3 and 2.4; equation (1), Theorems 1, 2 and 3.
