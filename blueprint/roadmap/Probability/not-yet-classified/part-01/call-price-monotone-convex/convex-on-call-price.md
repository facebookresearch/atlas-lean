# Call prices are convex in strike

With nonnegative state prices, the call price is a
convex function of the strike on the whole real line (Atlas roadmap FI11.T04, convexity
half). Reuse: each summand is a nonnegative multiple of `K ↦ europeanCallPayoff (S ω) K`,
the max of an affine function and `0` (`ConvexOn.sup`, after unfolding
`europeanCallPayoff`); the sum of convex functions is convex. Do not
reprove `ConvexOn.sup`, `ConvexOn.smul`, or `ConvexOn.add`.
