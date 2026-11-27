# At an equilibrium, nullclines are tangent iff the loop gain is 1

For reals `α₁, α₂`, `β, γ ∈ ℕ` and an [equilibrium](is-equilibrium.md) `(u, v)` of the toggle switch
`u' = α₁ / (1 + v^β) − u`, `v' = α₂ / (1 + u^γ) − v`, the nullclines are
[tangent](nullclines-tangent.md) at `(u, v)` if and only if the [loop gain](loop-gain.md) `P` equals
`1`. Equivalently, `0` is an eigenvalue of the [Jacobian matrix](jacobian.md), whose determinant is
`1 − P`.
