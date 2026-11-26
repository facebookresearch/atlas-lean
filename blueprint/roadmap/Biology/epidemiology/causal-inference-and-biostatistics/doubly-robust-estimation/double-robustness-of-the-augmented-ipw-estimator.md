# Double robustness of the augmented inverse-probability-weighted estimator

Let $(X, R, RY)$ be observed, where $X$ are covariates, $R \in \{0, 1\}$ indicates that the outcome $Y$ is observed, and data are missing at random: $R \perp Y \mid X$. Write $\pi_0(X) = \Pr(R = 1 \mid X)$ and $m_0(X) = \mathbb{E}(Y \mid X)$, and assume overlap, $\pi_0(X) \ge \delta > 0$ almost surely, and $\mathbb{E}(Y^2) < \infty$. For working functions $m(X)$ with $\mathbb{E}\{m(X)^2\} < \infty$ and $\pi(X) \ge \delta' > 0$ almost surely, define

$$\psi(\pi, m) = \mathbb{E}\Bigl[\frac{R\, Y}{\pi(X)} - \frac{R - \pi(X)}{\pi(X)}\, m(X)\Bigr].$$

Then

$$\psi(\pi, m) - \mathbb{E}(Y) = \mathbb{E}\Bigl[\frac{\bigl(\pi_0(X) - \pi(X)\bigr)\bigl(m_0(X) - m(X)\bigr)}{\pi(X)}\Bigr],$$

so $\psi(\pi, m) = \mathbb{E}(Y)$ whenever $\pi = \pi_0$ or $m = m_0$. The lower bound on the working $\pi$ makes every expectation here finite; strict positivity alone does not: with $R$ an independent fair coin, $Y$ an independent random sign, $X$ uniform on $(0, 1)$ and $\pi(X) = X$, the outcome regression $m = m_0 = 0$ is correct but $RY/X$ has no expectation. This is a population identity. Consequently the estimator $\hat\mu_{\mathrm{DR}} = n^{-1} \sum_{i=1}^{n} \bigl[R_i Y_i / \hat\pi(X_i) - (R_i - \hat\pi(X_i)) \hat m(X_i) / \hat\pi(X_i)\bigr]$, with $\hat\pi$ and $\hat m$ fitted from parametric models, is consistent for $\mathbb{E}(Y)$ if at least one of the two models is correctly specified, provided the fitted models converge to limits $(\pi^*, m^*)$ (with $\pi^* = \pi_0$ or $m^* = m_0$), $\hat\pi$ is bounded below by a positive constant, and the usual regularity conditions for parametric M-estimation (a uniform law of large numbers over the working models) hold. The same construction applied to each treatment arm, with $R$ the treatment indicator and $Y$ the potential outcome, gives a doubly robust estimator of an average causal effect under no unmeasured confounding.

## Expansion

Write $\frac{RY}{\pi} - \frac{R - \pi}{\pi} m = Y + \frac{(R - \pi)(Y - m)}{\pi}$, using $RY = R \cdot Y$. Conditioning on $X$ and using $R \perp Y \mid X$, $\mathbb{E}\{(R - \pi)(Y - m) \mid X\} = (\pi_0 - \pi)(m_0 - m)$, which gives the product-of-errors identity. Either factor vanishing removes the bias, which is the defining property of double robustness.

## Sources

- H. Bang and J. M. Robins, *Doubly robust estimation in missing data and causal inference models*, Biometrics 61 (2005), 962–973. <https://doi.org/10.1111/j.1541-0420.2005.00377.x>
