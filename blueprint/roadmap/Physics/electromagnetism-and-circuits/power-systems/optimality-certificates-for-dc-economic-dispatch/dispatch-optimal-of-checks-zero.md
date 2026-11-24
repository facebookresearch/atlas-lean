# A certificate accepted with zero gap proves optimality

Consider a network with finitely many buses and branches (each branch with a tail and a head bus),
finitely many generators placed at buses, a reference bus `r`, and rational data: susceptances `b`,
demand `d`, generator limits `p_min`, `p_max`, flow limits `f_min`, `f_max` and costs `c`, and a
rational witness accepted by the [certificate checker](checks-dispatch-certificate.md) with budget
`ε = 0`. Then the real values of `(p, θ)` form a
[feasible dispatch](../dc-economic-dispatch-as-a-linear-program/is-dispatch-feasible.md) of the real
dispatch problem of the cast data (the canonical problem with the entrywise real values of `b`, `d`,
`p_min`, `p_max`, `f_min`, `f_max`), its cost `c · p` is at most the cost of every feasible real
dispatch, and `c · p = L`, the [certified lower bound](dual-lower-bound.md)
`L = d · λ + p_min · μ_lo - p_max · μ_hi + f_min · η_lo - f_max · η_hi`.
