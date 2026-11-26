# Central limit theorem for the score

Let $(\mathcal{X}, \nu)$ be a measure space and $p : \mathbb{R} \times \mathcal{X} \to \mathbb{R}$, $(\theta, x) \mapsto p_\theta(x)$, a one-parameter family of densities, with [score](score.md) $s_\theta(x) = \partial_\theta \log p_\theta(x)$, Fisher information $I(\theta) = \int (\partial_\theta p_\theta)^2 / p_\theta \, d\nu$ and $P_\theta$ the measure with density $\max(p_\theta, 0)$ with respect to $\nu$. Let $\theta_0 \in \mathbb{R}$ with $p_{\theta_0} > 0$ measurable and $t \mapsto p_t(x)$ differentiable at $\theta_0$ for every $x$, and assume that $s_{\theta_0}$ is measurable with $\int s_{\theta_0}^2 \, dP_{\theta_0} < \infty$ and $\int s_{\theta_0} \, dP_{\theta_0} = 0$. If $X_0, X_1, \dots$ are independent random variables on a probability space with law $P_{\theta_0}$, then

$$\frac{1}{\sqrt n} \sum_{i<n} s_{\theta_0}(X_i) \to N\big(0, I(\theta_0)\big) \quad \text{in distribution}.$$

## Sources

- E. L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed., Springer, 1998, §6.3.
- A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, Chapter 5.
