# The checker rejects a dual witness that is not dual feasible

Consider a network with finitely many buses and branches (each branch with a tail and a head bus),
finitely many generators placed at buses, a reference bus `r`, and rational data: susceptances `b`,
demand `d`, generator limits `p_min`, `p_max`, flow limits `f_min`, `f_max` and costs `c`, and a
rational witness: a dispatch `(p, θ)`, nodal prices `λ`, a reference multiplier `ρ`, bound
multipliers `μ_hi`, `μ_lo` (generators) and `η_hi`, `η_lo` (branches), and a gap budget `ε`. If the
witness is not [dual feasible](is-dual-feasible.md) (a negative bound multiplier or a failed
stationarity equation), the [certificate checker](checks-dispatch-certificate.md) rejects.
