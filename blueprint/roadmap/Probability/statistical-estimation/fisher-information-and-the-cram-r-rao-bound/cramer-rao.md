# Cramér–Rao inequality

Let $(\mathcal{X}, \nu)$ be a measure space, $\theta \in \mathbb{R}$, and $p_{\theta'} : \mathcal{X} \to [0, \infty)$, $\theta' \in \mathbb{R}$, nonnegative functions with $\int p_{\theta'}\, d\nu = 1$ for $\theta'$ near $\theta$. Write $\dot p_\theta(x)$ for the derivative of $\theta' \mapsto p_{\theta'}(x)$ at $\theta$ ($0$ where it does not exist). Assume $\dot p_\theta$ is almost everywhere strongly measurable with $\int \dot p_\theta^2/p_\theta\, d\nu < \infty$ (so the [Fisher information](fisher-information.md) $I(\theta)$ is finite). Let $T$ be an almost everywhere strongly measurable estimator with $\int T^2 p_\theta\, d\nu < \infty$ and $\int T p_{\theta'}\, d\nu = g(\theta')$ for $\theta'$ near $\theta$, and assume that $\int p_{\theta'}\, d\nu$ and $\int T p_{\theta'}\, d\nu$ have derivatives $\int \dot p_\theta\, d\nu$ and $\int T \dot p_\theta\, d\nu$ at $\theta$. Write $\operatorname{Var}_\theta T = \int (T - g(\theta))^2 p_\theta\, d\nu$. Assume moreover that $p_\theta$ is almost everywhere strongly measurable, that $\theta' \mapsto p_{\theta'}(x)$ is differentiable at $\theta$ for every $x$, and that $I(\theta) > 0$. Then

$$\operatorname{Var}_\theta T \ge \frac{g'(\theta)^2}{I(\theta)}.$$

These three additional hypotheses are not needed: see the [Cramér–Rao inequality with minimal hypotheses](cramer-rao-general.md).

## Sources

- H. Cramér, *Mathematical Methods of Statistics*, Princeton University Press, 1946, Chapter 32.
- C. R. Rao, *Information and the accuracy attainable in the estimation of statistical parameters*, Bull. Calcutta Math. Soc. 37 (1945), 81–91.
- E. L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed., Springer, 1998, Chapter 2.
