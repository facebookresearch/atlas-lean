# Without vital dynamics the system is the closed SEIR model

For all real `β, σ, γ, N` and all functions `S, E, I, R : ℝ → ℝ`, `(S, E, I, R)` is a
[solution](is-solution.md) of the SEIR system with vital dynamics for `μ = 0` if and only if it is a
[solution of the closed SEIR model](../seir-epidemic-model/is-solution.md): `S' = −β S I / N`,
`E' = β S I / N − σ E`, `I' = σ E − γ I`, `R' = γ I` for every `t ≥ 0`.
