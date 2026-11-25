# Cramér–Rao inequality for a real estimand of a vector parameter

Let $p_{\theta'}$, $\theta' \in \mathbb R^k$, be nonnegative probability densities with respect to a measure $\nu$ for $\theta'$ near $\theta$, differentiable in the parameter at $\theta$, with square-integrable partial scores $\partial_i p_\theta / p_\theta$ and positive definite Fisher information matrix

$$I(\theta)_{ij} = \int \frac{\partial_i p_\theta \, \partial_j p_\theta}{p_\theta} \, d\nu .$$

Let $T$ be an estimator with $\int T^2 p_\theta \, d\nu < \infty$ that is unbiased for $g(\theta')$ for $\theta'$ near $\theta$, and suppose that $\int p_{\theta'} \, d\nu$ and $\int T p_{\theta'} \, d\nu$ can be differentiated under the integral sign at $\theta$. Then

$$\nabla g(\theta)^{\mathsf T} \, I(\theta)^{-1} \, \nabla g(\theta) \le \operatorname{Var}_\theta T = \int (T - g(\theta))^2 \, p_\theta \, d\nu .$$

This is Rao's bound for one real-valued estimator $T$ of a real function $g$ of a vector parameter. The matrix form $\operatorname{Cov}_\theta(T) \succeq J I(\theta)^{-1} J^{\mathsf T}$ for a vector $T$ of estimators with Jacobian $J$ of its mean follows by applying the bound to every linear combination $c^{\mathsf T} T$ (under the same hypotheses for each combination), but it is not part of this statement. For $k = 1$ the statement corresponds to the [Cramér–Rao inequality](cramer-rao.md), identifying $\mathbb R^1$ with $\mathbb R$. The proof takes the [directional Cramér–Rao inequality](sq-inner-le-quad-form-mul.md), $\langle a, \nabla g(\theta)\rangle^2 \le (a^{\mathsf T} I(\theta) a) \operatorname{Var}_\theta T$ for every $a \in \mathbb R^k$, at $a = I(\theta)^{-1} \nabla g(\theta)$: both $\langle a, \nabla g\rangle$ and $a^{\mathsf T} I a$ then equal $c = \nabla g^{\mathsf T} I^{-1} \nabla g$, so $c^2 \le c \operatorname{Var}_\theta T$, and $c \le \operatorname{Var}_\theta T$ follows whether $c > 0$ or $c \le 0$.

## Background

- [Directional Cramér–Rao inequality](sq-inner-le-quad-form-mul.md): the bound along each direction, from which this one follows by linear algebra.
- [Hájek's convolution theorem](../asymptotic-efficiency-and-adaptive-estimation/hajek-convolution.md): the asymptotic counterpart, which bounds regular rather than unbiased estimators.

## Sources

- C. R. Rao, "Information and the accuracy attainable in the estimation of statistical parameters", *Bull. Calcutta Math. Soc.* 37 (1945) 81–91.
