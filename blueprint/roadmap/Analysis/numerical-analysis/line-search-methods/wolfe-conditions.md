# Standard Wolfe conditions

A step length satisfies the *standard Wolfe conditions* with constants $\delta$ and $\sigma$ if it
satisfies the [Armijo condition](armijo-condition.md) with constant $\delta$ and the
[curvature condition](curvature-condition.md) with constant $\sigma$; one usually takes
$0 < \delta < \sigma < 1$, which guarantees that such steps exist for a descent direction when
$f$ is continuously differentiable and bounded below along the ray (Wolfe).

With $s = \alpha d$ and $y = \nabla f(x + s) - \nabla f(x)$, the curvature condition gives
$s^\top y \ge (\sigma - 1)\, \alpha\, \nabla f(x)^\top d > 0$ for a descent direction: this is
why Wolfe steps keep quasi-Newton updates positive definite.

## Background

- [The BFGS update preserves positive definiteness under the curvature condition](../quasi-newton-methods/bfgs-update-pos.md):
  the condition $s^\top y > 0$ that Wolfe steps supply.

## Sources

- Y. H. Dai and Y. Yuan, *A nonlinear conjugate gradient method with a strong global convergence property*, SIAM J. Optim. 10 (1999), 177–182, conditions (1.7) and (1.10).
