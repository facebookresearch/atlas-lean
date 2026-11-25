# Global forward existence for matrix games

For a finite set `ι` of strategies, a payoff matrix `A` on `ι` and a point `x₀` of the simplex
(`x₀_i ≥ 0`, `∑_i x₀_i = 1`), there is a [solution](../replicator-dynamics/is-solution.md) `x` of
the replicator equation `x_i' = x_i ((A x)_i - x · A x)` for `t ≥ 0` with `x(0) = x₀`. The proof
multiplies the field by a smooth bump function equal to `1` near the simplex, applies the global
existence theorem for globally Lipschitz fields, and uses that the simplex is invariant.
