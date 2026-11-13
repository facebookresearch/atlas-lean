# Is Min On of karush kuhn tucker convex affine

Convex KKT sufficiency with affine equality constraints (MF11.3a). Minimize `f` subject to
`g i y ≤ 0` and `h j y = 0`, where `f` and every `g i` are convex on the whole space, every `h j`
is affine (convex and concave on the whole space), and all of them are differentiable at `x`.
If `x` satisfies the equality constraints and `lam i ≥ 0` and `mu j` (of either sign) satisfy
complementary slackness `lam i * g i x = 0` and stationarity
`fderiv ℝ f x + ∑ i, lam i • fderiv ℝ (g i) x + ∑ j, mu j • fderiv ℝ (h j) x = 0`, then
`f x ≤ f y` for every feasible `y`; so a feasible `x` is a global minimizer of `f` on the feasible
set. The inequality constraints need not hold at `x` for this bound. No constraint qualification
is needed. The mechanism is the first-order inequality `ConvexOn.add_fderiv_sub_le`; without
equality constraints (`p = 0`) this is the bound of ATLAS's
`MathlibExt.Analysis.Convex.KarushKuhnTucker.isMinOn_of_karush_kuhn_tucker_convex`.

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization* (2004), §5.5.3.
