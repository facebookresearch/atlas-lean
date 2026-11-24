# Local attraction of an interior evolutionarily stable state

For a finite set `ι` of strategies, a payoff matrix `A` on `ι` and an
[evolutionarily stable state](is-ess.md) `p` with `p_i > 0` for every `i`, there is `δ > 0` such
that every [solution](../replicator-dynamics/is-solution.md) `x` of the replicator equation
`x_i' = x_i ((A x)_i - x · A x)` for `t ≥ 0` with `x(0)` in the simplex and `‖x(0) - p‖ < δ`
converges to `p` as `t → ∞`, where `‖v‖ = max_i |v_i|` (Hofbauer and Sigmund 1998, Theorem 7.2.4,
interior case).
