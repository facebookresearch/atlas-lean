# Maximum-likelihood estimation of the negative binomial dispersion parameter

For $m > 0$ and $k > 0$ the negative binomial law $\mathrm{NB}(m, k)$ on $\{0, 1, 2, \dots\}$ is

$$\mathbb{P}(X = x) = \frac{\Gamma(k + x)}{\Gamma(k)\, x!} \left(\frac{k}{k + m}\right)^{k} \left(\frac{m}{k + m}\right)^{x}, \tag{1}$$

with mean $m$ and variance $m(1 + m/k)$. It is the Poisson–gamma mixture: if $g \sim \mathrm{Gamma}$ with mean $m$ and shape $k$, and $X \mid g \sim \mathrm{Poisson}(g)$, then $X \sim \mathrm{NB}(m, k)$. The Poisson law is the limit $k \to \infty$, and $k = 1$ gives the geometric law.

Let $x_1, \dots, x_n$ be independent $\mathrm{NB}(m, k)$ observations, not all zero, and reparameterize by $\alpha = 1/k$.

1. **Mean.** For every fixed $k > 0$ the likelihood is maximized in $m$ at the sample mean $\hat m = \bar x$. Indeed, the score in $m$ is

$$\sum_{i=1}^{n} \left(\frac{x_i}{m} - \frac{x_i + k}{m + k}\right) = \frac{k}{m(m + k)} \sum_{i=1}^{n} x_i - \frac{n k}{m + k},$$

which vanishes exactly at $m = \bar x$.
2. **Dispersion.** $\hat\alpha$ maximizes the log-likelihood in $\alpha$ with $m = \bar x$, numerically, over $\alpha > 0$, and $\hat k = 1/\hat\alpha$; underdispersed samples (sample variance below the mean) are assigned the boundary $\hat\alpha \to 0$, i.e. $\hat k \to \infty$.
3. **Interval.** With $\sigma_{\hat\alpha}$ the asymptotic standard error from the inverse information, the $1 - 2q$ Wald interval for $\alpha$ is $[\hat\alpha - z_{1-q}\sigma_{\hat\alpha},\ \hat\alpha + z_{1-q}\sigma_{\hat\alpha}]$; the interval for $k$ is obtained by inverting the endpoints and reversing their order, with upper limit $k = \infty$ when $\hat\alpha - z_{1-q}\sigma_{\hat\alpha} < 0$. By the delta method, $\sigma^2_{\hat k} \approx \sigma^2_{\hat\alpha} / \hat\alpha^4$.
4. **Moment estimator.** The method-of-moments estimator is $\hat k_{\mathrm{mom}} = \bar x^2 / (s^2 - \bar x)$, with $s^2$ the sample variance.

Working with $\alpha$ removes the discontinuity at homogeneous data ($\alpha \to 0$ instead of $k \to \infty$), extends continuously to underdispersion ($\alpha < 0$), and gives a more symmetric sampling distribution than $k$.

## Expansion

Simulation over $m \in \{0.5, 1, 3\}$, $k \in \{0.1, \dots, 10\}$ and $n \in \{10, 30, 100, 300\}$ shows that $\hat k$ is biased upward in small samples (small samples rarely contain values from the long right tail, so they look more homogeneous), with bias decreasing in $n$ and $m$. Realized coverage of nominal 90% intervals is usually below 90%, and almost all coverage failures are overestimates of $k$. For $k \le 1$, $n \ge 100$ gives accurate estimates and $n = 10$ is unreliable. Since none of the mechanisms studied biases $\hat k$ downward, overestimating the degree of overdispersion is rare. Pooling heterogeneous groups is the exception: it lowers the dispersion estimate.

## Sources

- J. O. Lloyd-Smith, "Maximum likelihood estimation of the negative binomial dispersion parameter for highly overdispersed data, with applications to infectious diseases", PLoS ONE 2(2) (2007) e180, Introduction, Eq. (1), Methods sections 2.1.1 and 2.2, Results section 3.1, and Discussion, <https://doi.org/10.1371/journal.pone.0000180> (PMC1791715).
