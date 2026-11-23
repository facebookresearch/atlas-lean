# Rao's score test, known information

**Setting.** Let $(\mathcal{X}, \nu)$ be a measure space, $p : \mathbb{R} \times \mathcal{X} \to \mathbb{R}$, $(\theta, x) \mapsto p_\theta(x)$, a one-parameter family of densities, $P_\theta$ the measure with density $\max(p_\theta, 0)$ with respect to $\nu$, $s_\theta(x) = \partial_\theta \log p_\theta(x)$ the score and $I(\theta) = \int (\partial_\theta p_\theta)^2 / p_\theta \, d\nu$ the Fisher information. Let $X_0, X_1, \dots$ be independent random variables on a probability space $(\Omega, P)$, each with law $P_{\theta_0}$.

Assume that $p_{\theta_0}(x) > 0$ for every $x$, that $p_{\theta_0}$ is measurable, that $\theta \mapsto p_\theta(x)$ is differentiable at $\theta_0$ for every $x$, that $s_{\theta_0}$ is measurable with $\mathbb{E}[s_{\theta_0}(X_0)^2] < \infty$ and $\mathbb{E}[s_{\theta_0}(X_0)] = 0$, and that $I(\theta_0) > 0$. Then the score statistic

$$\frac{1}{I(\theta_0)} \Big(\frac{1}{\sqrt{n}} \sum_{i=0}^{n-1} s_{\theta_0}(X_i)\Big)^2$$

converges in distribution to $\chi^2_1$ as $n \to \infty$.

## Sources

- C. R. Rao, *Large sample tests of statistical hypotheses concerning several parameters with applications to problems of estimation*, Proc. Cambridge Philos. Soc. 44 (1948), 50–57, one-parameter case.
- E. L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed., Springer, 1998, §6.3 (central limit theorem for the score).
