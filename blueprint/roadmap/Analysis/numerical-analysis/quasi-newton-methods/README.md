# Quasi-Newton methods

Quasi-Newton methods replace the Hessian in Newton's method by an approximation $B_k$ updated from the step $s_k = x_{k+1} - x_k$ and the gradient change $y_k = \nabla f(x_{k+1}) - \nabla f(x_k)$ so that the secant equation $B_{k+1} s_k = y_k$ holds. The BFGS update is a symmetric rank-two correction that keeps $B_k$ positive definite exactly when the curvature condition $s_k^\top y_k > 0$ holds, which the Wolfe line search guarantees.

- [BFGS update](bfgs-update.md)
- [The BFGS update satisfies the secant equation](bfgs-update-apply-self.md)
- [The BFGS update preserves symmetry](bfgs-update-symm.md)
- [The BFGS update preserves positive definiteness under the curvature condition](bfgs-update-pos.md)
- [Curvature is necessary for a positive definite secant update](inner-pos-of-bfgs-update-pos.md)

## Related topics

- [Newton's method for minimization](../../convex-analysis-and-variations/newton-s-method-for-minimization/README.md): the method
  whose Hessian quasi-Newton methods approximate.
- [Newton's method](../newton-s-method/README.md) for root finding: in one dimension the secant
  equation turns it into the secant method.
- [Line search methods](../line-search-methods/README.md): Wolfe steps supply the curvature condition.
- [Barzilai–Borwein step size](../barzilai-borwein-step-size/README.md): the secant equation fitted
  by a multiple of the identity.
