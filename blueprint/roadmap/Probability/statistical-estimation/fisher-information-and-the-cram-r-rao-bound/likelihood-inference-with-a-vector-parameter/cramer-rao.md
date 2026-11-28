# Cramér–Rao inequality with nonsingular information

Let $p_{\theta'}$, for $\theta'$ in a finite-dimensional real inner product space, be functions with $p_{\theta'}(x) > 0$ for every $\theta'$ and $x$, $\int p_{\theta'}\,d\nu = 1$ for $\theta'$ near $\theta$, $p_\theta$ measurable, and $\theta' \mapsto p_{\theta'}(x)$ differentiable at $\theta$ for every $x$, with a measurable score $s_\theta$ of finite second moment under $P_\theta$, and let $T$ be an estimator with finite second moment, unbiased for $g(\theta')$ for $\theta'$ near $\theta$, with $g$ differentiable at $\theta$. Suppose the differentiation under the integral sign holds in every direction and $I(\theta)$ is invertible. Then

$$\operatorname{Var}_\theta(T) \ge \big\langle\nabla g(\theta), I(\theta)^{-1}\nabla g(\theta)\big\rangle.$$

For singular information this form is not claimed; the directional form still applies.

## Sources

- Rao (1945), Cramér (1946), ch. 32; Lehmann & Casella (1998), Theorem 2.6.6.
