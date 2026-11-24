# First-order conditions for convexity and optimality

A differentiable function is convex exactly when each of its first-order Taylor approximations is a global underestimator, $f(x) \ge f(a) + Df(a)(x - a)$. This one inequality turns local information into global information: it gives the optimality criterion $Df(a)(x - a) \ge 0$ for minimizing a convex function over a convex set, it shows that stationary points of convex functions are global minimizers, and it is the step that turns stationarity of the Lagrangian into optimality in [Lagrange duality](../lagrange-duality/README.md) and the KKT conditions.

- [First-order condition for convexity](add-fderiv-le-of-convex-on.md)
- [Supporting affine minorants imply convexity](convex-on-of-forall-add-le.md)
- [First-order characterization of convexity](convex-on-iff-forall-add-fderiv-le.md)
- [Optimality criterion for convex problems](is-min-on-iff-forall-fderiv-nonneg.md)
- [Stationary points of convex functions are global minimizers](is-min-on-of-has-fderiv-at-eq-zero.md)

The MA-ProofBench formulation for $C^2$ functions on an open convex subset of a Banach space is the article [Convexity via the tangent-plane inequality](../convex-on-iff-forall-le-add-fderiv-withi.md), proved as a corollary.

## Related topics

- [Second-order condition for convexity](../second-order-condition-for-convexity/README.md)
- [Lagrange duality](../lagrange-duality/README.md)
- [Gradient descent](../gradient-descent/README.md)
- [Least squares, ridge and lasso regression](../../../ComputerScience/machine-learning/supervised-learning/least-squares-ridge-and-lasso-regression/README.md)
