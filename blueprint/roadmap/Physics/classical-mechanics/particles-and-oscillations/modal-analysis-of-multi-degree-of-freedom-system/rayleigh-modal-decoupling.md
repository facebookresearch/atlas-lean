# Rayleigh modal decoupling

Rayleigh-damped modal decoupling: for a complete mass-orthonormal basis `Φ` of the
pencil `(K, M)` with `Φᵀ * K * Φ = diagonal μ`, a trajectory `x` satisfies
`M x'' + (α M + β K) x' + K x = f` at time `t` iff its modal coordinates
`q = Φᵀ * M *ᵥ x` satisfy the decoupled equations
`q_j'' + (α + β * μ j) q_j' + μ j q_j = (Φᵀ *ᵥ f t) j` at `t`, for every mode `j`.
Proportional damping only; holds for every real `α`, `β` and any load `f`.
