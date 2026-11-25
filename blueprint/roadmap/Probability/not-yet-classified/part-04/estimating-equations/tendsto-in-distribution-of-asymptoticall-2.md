# Normal limit of an asymptotically linear estimator (vector)

Let $X_0, X_1, \dots$ be independent random variables on a probability space with common law $\mu_X$, and let $\theta$ and the almost-everywhere measurable estimators $\hat\theta_n$ take values in a finite-dimensional real inner product space $E$. Let $\varphi$ be an influence function for $\mu_X$ (measurable, integrable, square integrable, mean zero), and suppose

$$\sqrt n(\hat\theta_n - \theta) - n^{-1/2}\sum_{i<n}\varphi(X_i) \to 0 \text{ in probability.}$$

If $Y$ is an almost-everywhere measurable random vector in $E$ on a probability space with $\langle Y, t\rangle \sim N\bigl(0, \mathbb E\langle\varphi(X), t\rangle^2\bigr)$ for every $t \in E$, where $X \sim \mu_X$, then $\sqrt n(\hat\theta_n - \theta)$ converges in distribution to $Y$.
