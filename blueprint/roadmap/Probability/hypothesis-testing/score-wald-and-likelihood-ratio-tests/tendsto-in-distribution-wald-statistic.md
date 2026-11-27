# Wald's test

In the setting of [Rao's score test](tendsto-in-distribution-score-statistic.md) ($X_0, X_1, \dots$ independent with law $P_{\theta_0}$ on a probability space $(\Omega, P)$), write $\ell_n(\theta) = \sum_{i<n} \log p_\theta(X_i)$ and assume the following regularity conditions (R):

- $\delta > 0$, $p_\theta(x) > 0$ for all $\theta, x$, and $p_{\theta_0}$ is measurable;
- for every $x$ and every $\theta$ with $|\theta - \theta_0| < \delta$, the maps $t \mapsto \log p_t(x)$, $t \mapsto s_t(x)$ and $t \mapsto \partial_t s_t(x)$ are differentiable at $\theta$, and $|\partial_\theta^2 s_\theta(x)| \le M(x)$ for a measurable, $P_{\theta_0}$-integrable function $M$;
- $s_{\theta_0}$ is measurable with $\mathbb{E}[s_{\theta_0}(X_0)^2] < \infty$ and $\mathbb{E}[s_{\theta_0}(X_0)] = 0$;
- $\partial_\theta s_{\theta_0}$ is measurable and integrable with $\mathbb{E}[\partial_\theta s_{\theta_0}(X_0)] = -I(\theta_0)$, and $I(\theta_0) > 0$;
- $\hat\theta_n : \Omega \to \mathbb{R}$ are almost everywhere measurable, solve the likelihood equation with probability tending to one, $P\big(\sum_{i<n} s_{\hat\theta_n}(X_i) \ne 0\big) \to 0$, and are consistent, $\hat\theta_n \to \theta_0$ in probability.

The normalisation $\int p_\theta \, d\nu = 1$ is not assumed. Then the Wald statistic converges in distribution:

$$n (\hat\theta_n - \theta_0)^2 I(\theta_0) \to \chi^2_1.$$

## Sources

- A. Wald, *Tests of statistical hypotheses concerning several parameters when the number of observations is large*, Trans. Amer. Math. Soc. 54 (1943), 426–482, one-parameter case.
- E. L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed., Springer, 1998, §6.3 (asymptotic normality of consistent roots of the likelihood equation).
