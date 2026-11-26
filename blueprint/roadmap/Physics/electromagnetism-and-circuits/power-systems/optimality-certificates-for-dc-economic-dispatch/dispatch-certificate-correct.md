# An accepted certificate gives an ε-optimal dispatch

Consider a network with finitely many buses and branches (each branch with a tail and a head bus),
finitely many generators placed at buses, a reference bus `r`, and rational data: susceptances `b`,
demand `d`, generator limits `p_min`, `p_max`, flow limits `f_min`, `f_max` and costs `c`, and a
rational witness: a dispatch `(p, θ)`, nodal prices `λ`, a reference multiplier `ρ`, bound
multipliers `μ_hi`, `μ_lo` (generators) and `η_hi`, `η_lo` (branches), and a gap budget `ε` accepted
by the [certificate checker](checks-dispatch-certificate.md). Then, for the real dispatch problem of
the cast data (the canonical problem with the entrywise real values of `b`, `d`, `p_min`, `p_max`,
`f_min`, `f_max`) with the real costs and the [certified lower bound](dual-lower-bound.md)
`L = d · λ + p_min · μ_lo - p_max · μ_hi + f_min · η_lo - f_max · η_hi`:

- the real values of `(p, θ)` form a
  [feasible dispatch](../dc-economic-dispatch-as-a-linear-program/is-dispatch-feasible.md);
- `L ≤ c · p'` for every feasible real dispatch `(p', θ')`;
- `0 ≤ c · p - L ≤ ε`;
- `c · p ≤ c · p' + ε` for every feasible real dispatch `(p', θ')`.

Here `c · p` is computed from the real values of the rational costs and generation.
