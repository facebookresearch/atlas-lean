# Is Min On of karush kuhn tucker convex

Convex KKT sufficiency, with the sign conventions of `karush_kuhn_tucker_inequality`
(minimize `f` subject to `g i y ≤ 0`). If `f` and every `g i` are convex on the whole space and
differentiable at `x`, and multipliers `lam` satisfy `lam i ≥ 0`, complementary slackness
`lam i * g i x = 0`, and stationarity `fderiv ℝ f x + ∑ i, lam i • fderiv ℝ (g i) x = 0`, then
`f x ≤ f y` for every feasible `y`. Feasibility of `x` itself is not needed for this bound;
when `x` is feasible, it is a global minimizer on the feasible set. No constraint qualification
is needed. An affine equality constraint `a y = 0`
can be encoded as the two convex constraints `a y ≤ 0` and `-a y ≤ 0`.

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization* (2004), §5.5.3.
