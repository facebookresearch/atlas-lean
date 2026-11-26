# Gradient descent

- [Sublinear rate of gradient descent for smooth convex functions](gradient-descent-convex-sublinear-rate.md)
- [Gradient descent with a step schedule](gradient-descent-trajectory.md)
- [Convex functions with $1$-Lipschitz gradient](is-unit-smooth-convex.md)
- [Uniform last-iterate rate of a step schedule](gradient-descent-uniform-rate.md)
- [The gradient descent exponent](gradient-descent-exponent.md)
- [Silver ratio](gradient-descent-silver-ratio.md)
- [Silver exponent](silver-gradient-descent-exponent.md)
- [Silver step schedule](silver-gradient-descent-schedule.md)
- [Constant unit steps achieve exponent one](gradient-descent-uniform-rate-one.md)
- [The gradient descent exponent is at least one](one-le-gradient-descent-exponent.md)
- [Gradient descent with zero step sizes stays put](gradient-descent-trajectory-zero-schedul.md)
- [Descent lemma](gradient-descent-descent-lemma.md)
- [Sufficient decrease of a gradient step](gradient-descent-sufficient-decrease.md)
- [Gradient norm bound for smooth lower-bounded functions](gradient-descent-norm-gradient-sq-le.md)
- [Convergence of the subgradient method](subgradient-method-rate.md)
- [Convergence of stochastic gradient descent](integral-sgd-average-sub-le.md)

## Strongly convex functions

- [First-order condition for strong convexity](add-inner-add-le-of-strong-convex-on.md)
- [Suboptimality bound from strong convexity](sub-le-norm-sq-div-of-strong-convex-on.md)
- [Strong convexity modulus is at most the smoothness constant](le-of-strong-convex-on-of-lipschitz-with.md)
- [Linear convergence of gradient descent for strongly convex functions](gradient-descent-strongly-convex-linear.md)
- [Linear convergence of gradient descent under the Polyak–Łojasiewicz inequality](linear-convergence-under-the-polyak-lojasiewicz-inequality.md)

## Expansiveness of the gradient step

How far the gradient update $G(w) = w - \alpha \nabla f(w)$ can move two points apart; these properties drive the stability analysis of stochastic gradient descent.

- [Co-coercivity of the gradient](inner-gradient-sub-ge.md)
- [The gradient update is $(1 + \alpha\beta)$-expansive](norm-gradient-step-sub-le-one-add-mul.md)
- [The gradient update of a convex smooth function is non-expansive](norm-gradient-step-sub-le.md)
- [The gradient update of a Lipschitz function is $\alpha L$-bounded](norm-smul-gradient-le.md)

## Nonconvex stochastic gradients

- [Nonconvex stochastic gradients: unbiased oracles and ABC expected smoothness](nonconvex-stochastic-gradients/README.md)

## Related topics

- [First-order conditions for convexity and optimality](../first-order-conditions-for-convexity/README.md)
- [Least squares, ridge and lasso regression](../../../ComputerScience/machine-learning/supervised-learning/least-squares-ridge-and-lasso-regression/README.md): the convex objectives of linear prediction to which these rates apply; for least squares the smoothness constant is the largest eigenvalue of the empirical covariance.
- [Generalization bounds and concentration](../../../ComputerScience/machine-learning/generalization-bounds-and-concentration/README.md): the $1/\sqrt{n}$ estimation error that the $1/\sqrt{t}$ rate of stochastic gradient descent matches.
- [Line search methods](../../numerical-analysis/line-search-methods/README.md): step lengths chosen
  by the Armijo and Wolfe conditions instead of a fixed schedule, and the Zoutendijk condition.
- [Barzilai–Borwein step size](../../numerical-analysis/barzilai-borwein-step-size/README.md):
  gradient descent with the two-point step size, a scalar fit of the secant equation.
- [Algorithmic stability](../../../ComputerScience/machine-learning/generalization-bounds-and-concentration/algorithmic-stability/README.md): the expansiveness properties of the gradient step make stochastic gradient descent on convex, smooth, Lipschitz losses uniformly stable, which bounds its generalization gap by $2L^2/n$ times its total step length for a loss bounded at the starting point.
- [Mirror descent](../mirror-descent/README.md): the subgradient method with a non-Euclidean proximal setup (a norm and a strongly convex distance-generating function), of which the Euclidean subgradient method and stochastic gradient descent are special cases.
- [Accelerated gradient methods](../accelerated-gradient-methods/README.md): Nesterov's method, which couples a gradient step with a dual-averaging step to improve the $O(1/k)$ rate to $O(1/k^2)$ under the same hypotheses, and its continuous-time limit.
