# The encoded witness passes the primal test iff it is feasible

Consider a network with finitely many buses and branches (each branch with a tail and a head bus),
finitely many generators placed at buses, a reference bus `r`, and rational data: susceptances `b`,
demand `d`, generator limits `p_min`, `p_max`, flow limits `f_min`, `f_max` and costs `c`, and a
rational dispatch `(p, θ)`. The [rational encoded point](rat-encode.md) `x` satisfies `x ≥ 0` and
`A x ≤ rhs` for the [rational LP matrix](rat-lp-matrix.md) and [right-hand side](rat-lp-rhs.md) if
and only if the real values of `(p, θ)` form a
[feasible dispatch](../dc-economic-dispatch-as-a-linear-program/is-dispatch-feasible.md) of the real
dispatch problem of the cast data (the canonical problem with the entrywise real values of `b`, `d`,
`p_min`, `p_max`, `f_min`, `f_max`).
