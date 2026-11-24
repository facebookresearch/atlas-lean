# Accepted witnesses are exactly the feasible ones within the gap budget

Consider a network with finitely many buses and branches (each branch with a tail and a head bus),
finitely many generators placed at buses, a reference bus `r`, and rational data: susceptances `b`,
demand `d`, generator limits `p_min`, `p_max`, flow limits `f_min`, `f_max` and costs `c`, and a
rational witness: a dispatch `(p, θ)`, nodal prices `λ`, a reference multiplier `ρ`, bound
multipliers `μ_hi`, `μ_lo` (generators) and `η_hi`, `η_lo` (branches), and a gap budget `ε`. The
[certificate checker](checks-dispatch-certificate.md) accepts if and only if

- the real values of `(p, θ)` form a
  [feasible dispatch](../dc-economic-dispatch-as-a-linear-program/is-dispatch-feasible.md) of the
  real dispatch problem of the cast data (the canonical problem with the entrywise real values of
  `b`, `d`, `p_min`, `p_max`, `f_min`, `f_max`);
- the witness `(λ, ρ, μ_hi, μ_lo, η_hi, η_lo)` is [dual feasible](is-dual-feasible.md);
- `0 ≤ c · p - L ≤ ε`, with the [certified lower bound](dual-lower-bound.md)
  `L = d · λ + p_min · μ_lo - p_max · μ_hi + f_min · η_lo - f_max · η_hi`.
