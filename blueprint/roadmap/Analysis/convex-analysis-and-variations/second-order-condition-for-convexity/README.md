# Second-order condition for convexity

A twice differentiable function on an open convex set is convex exactly when its Hessian is positive semidefinite everywhere, $\nabla^2 f(y) \succeq 0$: its graph curves upward in every direction. The proof restricts $f$ to lines, where it reduces to the one-dimensional fact that a function with nonnegative second derivative has a nondecreasing derivative; the converse uses the [first-order condition](../first-order-conditions-for-convexity/README.md). The strengthened bounds $mI \preceq \nabla^2 f \preceq MI$ drive the convergence analysis of [gradient descent](../gradient-descent/README.md) and [Newton's method](../newton-s-method-for-minimization/README.md).

- [Positive semidefinite Hessian implies convexity](convex-on-of-hessian-nonneg.md)
- [Convexity implies a positive semidefinite Hessian](hessian-nonneg-of-convex-on.md)
- [Second-order characterization of convexity](convex-on-iff-hessian-nonneg.md)

## Related topics

- [First-order conditions for convexity and optimality](../first-order-conditions-for-convexity/README.md)
- [Positive definite matrices and matrix inequalities](../../../LinearAlgebra/positive-definite-matrices/README.md)
