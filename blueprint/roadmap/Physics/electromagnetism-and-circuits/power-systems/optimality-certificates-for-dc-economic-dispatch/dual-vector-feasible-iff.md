# The dual vector passes the dual test iff the witness is dual feasible

For a network with rational susceptances, generators at buses, a reference bus, costs `c`, and
rational prices `λ`, reference multiplier `ρ` and bound multipliers `μ_hi`, `μ_lo`, `η_hi`, `η_lo`,
the [dual vector](dual-vector.md) `y` satisfies `y ≥ 0` and `c_LP ≤ Aᵀ y` for the
[rational objective](rat-lp-objective.md) and [LP matrix](rat-lp-matrix.md) if and only if the
witness is [dual feasible](is-dual-feasible.md).
