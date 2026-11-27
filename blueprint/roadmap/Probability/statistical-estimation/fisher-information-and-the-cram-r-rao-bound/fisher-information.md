# Fisher information

Let $(\mathcal{X}, \nu)$ be a measure space and $(p_\theta)_{\theta \in \mathbb{R}}$ a one-parameter family of functions $p_\theta : \mathcal{X} \to \mathbb{R}$. The Fisher information at $\theta$ is

$$I(\theta) = \int_{\mathcal{X}} \frac{\big(\partial_\theta p_\theta(x)\big)^2}{p_\theta(x)}\, d\nu(x),$$

where $\partial_\theta p_\theta(x)$ is the derivative of $\theta' \mapsto p_{\theta'}(x)$ at $\theta$ ($0$ where it does not exist), division by $0$ gives $0$, and the integral is $0$ if the integrand is not integrable. Points with $p_\theta(x) = 0$ thus contribute $0$ (for a nonnegative family, $\partial_\theta p_\theta(x) = 0$ there).

## Sources

- H. Cramér, *Mathematical Methods of Statistics*, Princeton University Press, 1946, Chapter 32.
- C. R. Rao, *Information and the accuracy attainable in the estimation of statistical parameters*, Bull. Calcutta Math. Soc. 37 (1945), 81–91.
- E. L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed., Springer, 1998, Chapter 2.
