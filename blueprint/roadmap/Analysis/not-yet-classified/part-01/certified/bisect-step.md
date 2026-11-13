# Bisect Step

One bisection step on the rational bracket `I` with midpoint `m = I.mid`. The decision `true`
records `0 ≤ f m` and keeps `[I.lower, m]`; the decision `false` records `f m ≤ 0` and keeps
`[m, I.upper]`.
