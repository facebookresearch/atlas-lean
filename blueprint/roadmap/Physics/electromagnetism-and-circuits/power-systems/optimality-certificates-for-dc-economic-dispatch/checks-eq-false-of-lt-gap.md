# The checker rejects a witness whose gap exceeds the budget

Consider a network with finitely many buses and branches (each branch with a tail and a head bus),
finitely many generators placed at buses, a reference bus `r`, and rational data: susceptances `b`,
demand `d`, generator limits `p_min`, `p_max`, flow limits `f_min`, `f_max` and costs `c`, and a
rational witness: a dispatch `(p, θ)`, nodal prices `λ`, a reference multiplier `ρ`, bound
multipliers `μ_hi`, `μ_lo` (generators) and `η_hi`, `η_lo` (branches), and a gap budget `ε`. If
`ε < c · p - L`, with the [certified lower bound](dual-lower-bound.md)
`L = d · λ + p_min · μ_lo - p_max · μ_hi + f_min · η_lo - f_max · η_hi`, the
[certificate checker](checks-dispatch-certificate.md) rejects.
