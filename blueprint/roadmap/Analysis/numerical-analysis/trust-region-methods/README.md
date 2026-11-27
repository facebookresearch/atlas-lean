# Trust-region methods

A trust-region method computes a trial step by minimising a model of the objective, usually the quadratic $q(s) = g^\top s + \tfrac12 s^\top B s$, within a ball $\|s\| \le \Delta$, and accepts the step and adjusts the radius $\Delta$ according to the ratio of actual to predicted reduction. Global convergence rests on a sufficient decrease of the model, the Cauchy decrease $-q(s) \ge \tfrac12 \|g\| \min(\Delta, \|g\|/\|B\|)$; the global solutions of the subproblem are characterised by a multiplier $\mu \ge 0$ with $(B + \mu I)s = -g$, $B + \mu I$ positive semidefinite and $\mu(\Delta - \|s\|) = 0$.

- [Quadratic trust-region model](trust-region-model.md)
- [Cauchy decrease of the trust-region model](exists-cauchy-step.md)
- [Curvature bound from an operator-norm bound](inner-apply-self-le-of-op-norm-le.md)
- [Sufficient decrease of an exact trust-region step](pred-ge-of-is-min-on.md)
- [Sufficient optimality condition for the trust-region subproblem](trust-region-model-le-of-optimality.md)
- [Necessary optimality conditions for the trust-region subproblem](exists-optimality-of-is-min-on.md)

## Related topics

- [Line search methods](../line-search-methods/README.md): the alternative globalisation strategy.
- [Quasi-Newton methods](../quasi-newton-methods/README.md): a common source of the Hessian
  approximation $B$ in the model.
- [Newton's method for minimization](../../convex-analysis-and-variations/newton-s-method-for-minimization/README.md): the local method
  that trust-region steps reduce to when the radius is inactive and $B$ is the Hessian.
- [Self-concordant functions and barriers](../../convex-analysis-and-variations/self-concordant-functions-and-barriers/README.md): the unit Dikin ellipsoid, a region shaped by the local Hessian norm in which a self-concordant function stays defined and is bounded by explicit models.
