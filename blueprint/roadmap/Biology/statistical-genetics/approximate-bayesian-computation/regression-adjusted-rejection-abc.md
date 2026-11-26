# Regression-adjusted rejection approximate Bayesian computation

Let a model with parameter $\theta \in \mathbb R$ and prior $\pi(\theta)$ generate data whose summary statistics $s \in \mathbb R^d$ are observed as $s_{\mathrm{obs}}$. **Rejection ABC** draws $\theta_i \sim \pi$ and simulates $s_i$ from the model given $\theta_i$, for $i = 1, \dots, n$, and keeps the $\theta_i$ with $\|s_i - s_{\mathrm{obs}}\| \le \delta$ as an approximate sample from $p(\theta \mid s_{\mathrm{obs}})$. The **local-linear regression adjustment** weights each draw by the Epanechnikov kernel
$$K_\delta(t) = \begin{cases} c\,\delta^{-1}\big(1 - (t/\delta)^2\big), & t \le \delta,\\ 0, & t > \delta,\end{cases} \qquad t = \|s_i - s_{\mathrm{obs}}\|,$$
fits the weighted least-squares regression
$$(\hat\alpha, \hat b) = \arg\min_{\alpha, b} \sum_{i=1}^n \big(\theta_i - \alpha - (s_i - s_{\mathrm{obs}})^{\top} b\big)^2 K_\delta\big(\|s_i - s_{\mathrm{obs}}\|\big),$$
and replaces each accepted draw by
$$\theta_i^* = \theta_i - (s_i - s_{\mathrm{obs}})^{\top}\hat b,$$
with weight $K_\delta(\|s_i - s_{\mathrm{obs}}\|)$. The weighted $\theta_i^*$ approximate the posterior $p(\theta \mid s_{\mathrm{obs}})$, and $\hat\alpha$ estimates the posterior mean. Parameters on bounded ranges are transformed (e.g. by logarithm) before regression.

## Expansion

If, near $s_{\mathrm{obs}}$, $\theta = \alpha + (s - s_{\mathrm{obs}})^{\top}b + \varepsilon$ with $\varepsilon$ independent of $s$, then $\theta_i^* = \alpha + \varepsilon_i$ has exactly the conditional law of $\theta$ at $s = s_{\mathrm{obs}}$, so the adjustment removes the first-order bias from accepting draws with $s_i \ne s_{\mathrm{obs}}$. This permits a larger tolerance $\delta$, and so more accepted simulations, than plain rejection for the same accuracy. The method was introduced for population-genetic inference, where likelihoods of summary statistics such as numbers of segregating sites or alleles are intractable but simulation under the coalescent is easy.

## Sources

- M. A. Beaumont, W. Zhang, D. J. Balding, "Approximate Bayesian Computation in Population Genetics", Genetics 162 (2002), 2025–2035, <https://doi.org/10.1093/genetics/162.4.2025> (PMC1462356).
