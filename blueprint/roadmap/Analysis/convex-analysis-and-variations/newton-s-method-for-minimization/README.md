# Newton's method for minimization

Newton's method minimizes a twice differentiable convex function $f$ by stepping to the minimizer of its second-order model, $x^+ = x + \Delta x_{\mathrm{nt}}$ with $\nabla^2 f(x)\, \Delta x_{\mathrm{nt}} = -\nabla f(x)$. When the Hessian is $L$-Lipschitz and $\nabla^2 f \succeq m I$, each pure Newton step satisfies $\frac{L}{2m^2}\|\nabla f(x^+)\| \le \big(\frac{L}{2m^2}\|\nabla f(x)\|\big)^2$, so once $\frac{L}{2m^2}\|\nabla f(x)\| < 1$ the gradient converges to zero quadratically: the number of correct digits roughly doubles at each iteration. Newton's method is the inner solver of the barrier method; see the [duality gap of central points](../lagrange-duality/central-point-duality-gap.md).

- [Taylor remainder for a map with Lipschitz derivative](norm-sub-sub-le-of-lipschitz-fderiv.md)
- [One pure Newton step squares the gradient norm](norm-gradient-newton-step-le.md)
- [Quadratic convergence of the pure Newton method](newton-quadratic-convergence.md)

## Related topics

- [Newton's method (root finding)](../../numerical-analysis/newton-s-method/README.md)
- [Gradient descent](../gradient-descent/README.md)
- [Lagrange duality](../lagrange-duality/README.md)
- [Quasi-Newton methods](../../numerical-analysis/quasi-newton-methods/README.md): Newton-type
  methods that replace the Hessian by secant approximations such as BFGS.
- [Trust-region methods](../../numerical-analysis/trust-region-methods/README.md): globalisation of
  Newton's method by minimising its quadratic model over a ball.
- [Self-concordant functions and barriers](../self-concordant-functions-and-barriers/README.md): the affine-invariant condition under which Newton's method has a global complexity bound, the basis of interior-point methods.
