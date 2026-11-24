# Lagrange duality

For the problem of minimizing $f_0(x)$ over $x \in D$ subject to $f_i(x) \le 0$ ($i \in \iota$, finite), the Lagrangian $L(x, \mu) = f_0(x) + \sum_i \mu_i f_i(x)$ yields the dual function $g(\mu) = \inf_{x \in D} L(x, \mu)$, a lower bound on the optimal value $p^\star$ for every $\mu \ge 0$ (weak duality). For convex problems, Slater's condition (a strictly feasible point) closes the gap: $d^\star = \sup_{\mu \ge 0} g(\mu) = p^\star$, with a dual optimal $\mu$ when $p^\star > -\infty$. The proof separates two convex sets in the space of constraint and objective values. With differentiability, the [first-order condition](../first-order-conditions-for-convexity/README.md) makes the Karush–Kuhn–Tucker conditions sufficient for optimality, and the same argument bounds the suboptimality of the central points of the logarithmic barrier method by $m/t$, the basis of interior-point methods.

Equality constraints are not covered yet: Boyd–Vandenberghe's Slater theorem also allows affine equality constraints, with the strictly feasible point in the relative interior of $D$.

## Definitions

- [Lagrangian](lagrangian.md)
- [Lagrange dual function](dual-function.md)
- [Primal optimal value](primal-value.md)
- [Dual optimal value](dual-value.md)

## Weak duality

- [Lagrangian lower bound](lagrangian-le-of-feasible.md)
- [Lower bound property of the dual function](dual-function-le-of-feasible.md)
- [Weak duality](dual-value-le-primal-value.md)

## Strong duality under Slater's condition

- [Slater's theorem, multiplier form](exists-multiplier-of-slater.md)
- [Strong duality under Slater's condition](dual-value-eq-primal-value-of-slater.md)
- [Dual attainment under Slater's condition](exists-dual-function-eq-primal-value-of.md)

## Duals through conjugates

- [The dual function of a linearly constrained problem is minus a conjugate](dual-function-linear-eq-neg-sub-fenchel.md)

## Optimality conditions

- [Convexity of the Lagrangian](convex-on-lagrangian.md)
- [Derivative of the Lagrangian](has-fderiv-at-lagrangian.md)
- [The dual function at a stationary point of the Lagrangian](dual-function-eq-lagrangian-of-stationar.md)
- [Sufficiency of the KKT conditions for convex problems](kkt-sufficient.md)

## Interior-point methods

- [Duality gap of central points in the barrier method](central-point-duality-gap.md)

## Related topics

- [First-order conditions for convexity and optimality](../first-order-conditions-for-convexity/README.md)
- [Fenchel–Moreau theorem](../fenchel-moreau-theorem/README.md)
- [Linear programming](../../../Geometry/convex-geometry/linear-programming/README.md)
- [Moreau decomposition](../moreau-decomposition/README.md)
- [Newton's method for minimization](../newton-s-method-for-minimization/README.md)
- [Alternating direction method of multipliers](../alternating-direction-method-of-multipliers/README.md)
- [Self-concordant functions and barriers](../self-concordant-functions-and-barriers/README.md): the theory of barriers behind interior-point methods; the logarithmic barrier of $m$ linear inequalities is an $m$-self-concordant barrier.
