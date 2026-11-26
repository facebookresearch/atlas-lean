# Exact rational certificate checker for DC dispatch

Consider a network with finitely many buses and branches (each branch with a tail and a head bus),
finitely many generators placed at buses, a reference bus `r`, and rational data: susceptances `b`,
demand `d`, generator limits `p_min`, `p_max`, flow limits `f_min`, `f_max` and costs `c`, and a
rational witness: a dispatch `(p, θ)`, nodal prices `λ`, a reference multiplier `ρ`, bound
multipliers `μ_hi`, `μ_lo` (generators) and `η_hi`, `η_lo` (branches), and a gap budget `ε`. The
checker is a computable test returning true or false. It runs the exact rational linear-programming
gap test on the [rational LP matrix](rat-lp-matrix.md) `A`, the
[rational right-hand side](rat-lp-rhs.md) `rhs`, the [rational objective](rat-lp-objective.md)
`c_LP`, the [encoded witness](rat-encode.md) `x` and the [dual vector](dual-vector.md) `y`: it
accepts when `x ≥ 0`, `A x ≤ rhs`, `y ≥ 0`, `c_LP ≤ Aᵀ y` and `0 ≤ rhs · y - c_LP · x ≤ ε`. Its
acceptance condition is [characterised](checks-dispatch-certificate-eq-true-iff.md) in dispatch
terms.
