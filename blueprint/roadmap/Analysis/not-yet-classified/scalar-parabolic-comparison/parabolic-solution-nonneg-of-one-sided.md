# Parabolic solution nonneg of one Sided

Nonlinear comparison with one-sided control. Let `c` be a classical
solution of `c_t - D * c_xx = r(c, x, t)` on the parabolic interior
`(0, T] × (0, L)`, continuous on the closed cylinder `[0, T] × [0, L]`,
with `D ≥ 0`. Suppose the reaction is bounded below by `K * c` wherever
the solution is nonpositive, with one constant `K` uniform over the
cylinder. Then nonnegative initial data on `[0, L]` and nonnegative
Dirichlet data at `x = 0` and `x = L` on `[0, T]` give `c ≥ 0` on the
whole closed cylinder. The bound is evaluated only at values the solution
attains; quasi-positivity `r(0) ≥ 0` alone is not assumed to suffice.
Intended proof: negative-minimum argument for
`exp (-K * t) * c t x + ε * (1 + t)`, then `ε → 0`.
