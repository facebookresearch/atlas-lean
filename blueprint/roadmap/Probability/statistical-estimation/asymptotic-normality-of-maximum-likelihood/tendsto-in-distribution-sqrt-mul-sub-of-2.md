# Asymptotic normality of consistent roots of the likelihood equation

Let $(\mathcal{X}, \nu)$ be a measure space and $p : \mathbb{R} \times \mathcal{X} \to \mathbb{R}$, $(\theta, x) \mapsto p_\theta(x)$, a one-parameter family of densities, with [score](score.md) $s_\theta(x) = \partial_\theta \log p_\theta(x)$, Fisher information $I(\theta) = \int (\partial_\theta p_\theta)^2 / p_\theta \, d\nu$ and $P_\theta$ the measure with density $\max(p_\theta, 0)$ with respect to $\nu$. Let $\theta_0 \in \mathbb{R}$, $\delta > 0$ and assume Cramér's conditions:

- $p_\theta(x) > 0$ for all $\theta, x$, and for $|\theta - \theta_0| < \delta$ each $p_\theta$ is measurable with $\int p_\theta\, d\nu = 1$;
- for every $x$ and every $\theta$ with $|\theta - \theta_0| < \delta$, the maps $t \mapsto \log p_t(x)$, $t \mapsto s_t(x)$ and $t \mapsto \partial_t s_t(x)$ are differentiable at $\theta$, and $|\partial^2_\theta s_\theta(x)| \le M(x)$ for a measurable $P_{\theta_0}$-integrable $M$;
- $s_{\theta_0}$ is measurable, square integrable and has mean zero under $P_{\theta_0}$;
- $\partial_\theta s_{\theta_0}$ is measurable and integrable with $\int \partial_\theta s_{\theta_0}\, dP_{\theta_0} = -I(\theta_0)$ (the information identity), and $I(\theta_0) > 0$.

Let $X_0, X_1, \dots$ be independent with law $P_{\theta_0}$ on a probability space $(\Omega, P)$, and let $\hat\theta_n$ be almost everywhere measurable estimators that solve the likelihood equation with probability tending to one, $P\big(\sum_{i<n} s_{\hat\theta_n}(X_i) \ne 0\big) \to 0$, and converge to $\theta_0$ in probability. Then

$$\sqrt n\, (\hat\theta_n - \theta_0) \to N\big(0, I(\theta_0)^{-1}\big) \quad \text{in distribution}.$$

The proof uses measurability only at $\theta_0$ and does not use the normalisation $\int p_\theta\, d\nu = 1$: the limit theorem holds for roots of any criterion with these derivatives. The differentiability of $\log p_\theta(x)$ ensures that $s_\theta(x)$ is the true derivative on the ball. The two moment identities are what differentiating $\int p_\theta\, d\nu = 1$ twice under the integral sign gives; they are assumed directly. The roots need not maximize the likelihood; for a maximum-likelihood estimator, consistency and the likelihood equation must be established separately (for example, from an interior maximum of a differentiable likelihood).

## Sources

- H. Cramér, *Mathematical Methods of Statistics*, Princeton University Press, 1946, §33.3.
- E. L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed., Springer, 1998, Theorem 6.3.10.
- A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, Theorem 5.41.
