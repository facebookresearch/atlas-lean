# Normal limit of an asymptotically linear estimator (scalar)

Let $X_0, X_1, \dots$ be independent random variables on a probability space, each with law $\mu_X$, and let $\varphi$ be an influence function for $\mu_X$: measurable, square integrable, integrable, with mean zero. Let $\hat\theta_n$ be almost-everywhere measurable estimators and $\theta$ a real number such that

$$\sqrt n\,(\hat\theta_n - \theta) - \frac{1}{\sqrt n}\sum_{i < n} \varphi(X_i) \to 0$$

in probability. Then $\sqrt n\,(\hat\theta_n - \theta)$ converges in distribution to the normal law $N\bigl(0, \int \varphi^2\,d\mu_X\bigr)$.
