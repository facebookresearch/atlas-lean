# An accepted certificate solves the real linear program up to ε

Consider a network with finitely many buses and branches (each branch with a tail and a head bus),
finitely many generators placed at buses, a reference bus `r`, and rational data: susceptances `b`,
demand `d`, generator limits `p_min`, `p_max`, flow limits `f_min`, `f_max` and costs `c`, and a
rational witness: a dispatch `(p, θ)`, nodal prices `λ`, a reference multiplier `ρ`, bound
multipliers `μ_hi`, `μ_lo` (generators) and `η_hi`, `η_lo` (branches), and a gap budget `ε` accepted
by the [certificate checker](checks-dispatch-certificate.md). Then the real
[encoded point](../dc-economic-dispatch-as-a-linear-program/encode.md) `x` of the real values of
`(p, θ)` satisfies `x ≥ 0` and `A x ≤ rhs` for the real
[LP matrix](../dc-economic-dispatch-as-a-linear-program/lp-matrix.md) and
[right-hand side](../dc-economic-dispatch-as-a-linear-program/lp-rhs.md) of the real data, and every
real `z ≥ 0` with `A z ≤ rhs` has objective value at most that of `x` plus `ε`, for the real
[LP objective](../dc-economic-dispatch-as-a-linear-program/lp-objective.md) of the real costs.
