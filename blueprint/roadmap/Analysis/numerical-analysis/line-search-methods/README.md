# Line search methods

A line search method for minimising a smooth function iterates $x_{k+1} = x_k + \alpha_k d_k$ along a descent direction $d_k$ ($\nabla f(x_k)^\top d_k < 0$) with a step length $\alpha_k > 0$ chosen to give sufficient decrease (the Armijo condition) without being too short (the Wolfe curvature condition). Under these conditions the Zoutendijk condition $\sum_k (\nabla f(x_k)^\top d_k)^2 / \|d_k\|^2 < \infty$ holds; it is the summability argument behind the global convergence of steepest descent, quasi-Newton and nonlinear conjugate gradient methods.

- [Armijo sufficient decrease condition](armijo-condition.md)
- [Wolfe curvature condition](curvature-condition.md)
- [Standard Wolfe conditions](wolfe-conditions.md)
- [Strong Wolfe conditions](strong-wolfe-conditions.md)
- [Strong Wolfe steps are standard Wolfe steps](to-wolfe-conditions.md)
- [Zoutendijk condition](zoutendijk.md)

## Related topics

- [Nonlinear conjugate gradient methods](../nonlinear-conjugate-gradient-methods/README.md): their
  global convergence proofs combine the Zoutendijk condition with a bound on $\|d_k\|$.
- [Quasi-Newton methods](../quasi-newton-methods/README.md): Wolfe steps supply the curvature
  condition $s^\top y > 0$ that keeps BFGS positive definite.
- [Trust-region methods](../trust-region-methods/README.md): the other globalisation strategy, which
  controls the step length through the radius instead of a line search.
- [Gradient descent](../../convex-analysis-and-variations/gradient-descent/README.md): fixed-step gradient descent on smooth convex functions, the line-search
  method with $d_k = -\nabla f(x_k)$ and a constant step.
