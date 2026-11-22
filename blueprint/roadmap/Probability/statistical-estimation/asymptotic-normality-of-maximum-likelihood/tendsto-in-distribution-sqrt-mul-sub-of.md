# Asymptotic normality of a consistent root of an estimating equation

Let $(\Omega, P)$ be a probability space, $X_0, X_1, \dots : \Omega \to \mathcal{X}$ independent with common law $\mu_X$, and $\psi : \mathbb{R} \times \mathcal{X} \to \mathbb{R}$, $\delta > 0$, $\theta_0 \in \mathbb{R}$. Assume:

- for every $x$ and every $\theta$ with $|\theta - \theta_0| < \delta$, the maps $t \mapsto \psi_t(x)$ and $t \mapsto \partial_t \psi_t(x)$ are differentiable at $\theta$, and $|\partial_\theta^2 \psi_\theta(x)| \le M(x)$ for a measurable $\mu_X$-integrable $M$;
- $\psi_{\theta_0}$ is measurable with $\mathbb{E}\psi_{\theta_0}(X_0)^2 < \infty$ and $\mathbb{E}\psi_{\theta_0}(X_0) = 0$;
- $\partial_\theta \psi_{\theta_0}$ is measurable and integrable with $J = \mathbb{E}\,\partial_\theta\psi_{\theta_0}(X_0) \ne 0$;
- $\hat\theta_n$ are almost everywhere measurable estimators with $P\big(\sum_{i<n} \psi_{\hat\theta_n}(X_i) \ne 0\big) \to 0$ and $\hat\theta_n \to \theta_0$ in probability.

Then

$$\sqrt n\, (\hat\theta_n - \theta_0) \to N\Big(0, \frac{\mathbb{E}\psi_{\theta_0}(X_0)^2}{J^2}\Big) \quad \text{in distribution}.$$

## Sources

- A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, Theorem 5.41 (one-dimensional case).
- H. Cramér, *Mathematical Methods of Statistics*, Princeton University Press, 1946, §33.3.
- E. L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed., Springer, 1998, §6.3.
