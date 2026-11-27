# Stein's unbiased risk estimate

Let $X \sim \mathcal N_p(\theta, I)$ and consider the estimator $X + g(X)$, where each coordinate $g_i$ is square integrable and satisfies the hypotheses of [Stein's lemma, coordinate form](integral-sub-mul-pi-gaussian-real.md) in the $i$-th coordinate, with partial derivative $\partial_i g_i$. Then

$$\mathbb E \sum_i \bigl(X_i + g_i(X) - \theta_i\bigr)^2 = p + \mathbb E\Bigl[\sum_i g_i(X)^2 + 2 \sum_i \partial_i g_i(X)\Bigr],$$

so $U(x) = p + 2 \nabla \cdot g(x) + \|g(x)\|^2$ is an unbiased estimate of the risk. This is Johnstone's draft, Proposition 2.7, equation (2.61), which credits Stein (1981). Johnstone assumes weak differentiability and $\mathbb E|X_i g_i(X)| + \mathbb E|\partial_i g_i(X)| < \infty$; the statement above assumes everywhere-differentiable slices and square-integrable $g_i$ (which makes the risk finite).

## Informally uses

- [Stein's lemma, coordinate form](integral-sub-mul-pi-gaussian-real.md): Johnstone derives (2.61) from it by expanding the square.

## Sources

- I. M. Johnstone, *Gaussian Estimation: Sequence and Wavelet Models*, pre-publication draft of 16 September 2019, https://imjohnstone.su.domains/GE_09_16_19.pdf. Numbers refer to that draft.
- C. M. Stein, "Estimation of the mean of a multivariate normal distribution", *Ann. Statist.* 9 (1981) 1135–1151 (cited for attribution; not consulted for numbering).
