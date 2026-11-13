# Global forward existence for matrix games

Through every point `x₀` of the simplex there
is a solution of the replicator equation `x_i' = x_i ((A x)_i - x · A x)` on `[0, ∞)`.

Proof: replace the fitness by `φ(y) • A y` for a smooth bump `φ` equal to `1` on the closed
ball of radius `2` around `0` (which contains the simplex). The resulting replicator field is
`φ(y)` times the original one, smooth with compact support, hence globally Lipschitz, so
`ode_global_exists_of_global_lipschitz` gives a global solution. It solves the replicator
equation of the truncated fitness, so it stays in the simplex (`IsSolution.mem_simplex`),
where `φ = 1`; hence it solves the original equation.
