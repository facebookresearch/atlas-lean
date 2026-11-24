# The Lotka–Volterra trajectory solves the Lotka–Volterra equation

For a finite set `ι`, a payoff matrix `A` on the strategies `ι ∪ {o}` and a
[replicator solution](../replicator-dynamics/is-solution.md) `x` of the game,
`x_k' = x_k ((A x)_k - f̄(x))` for `t ≥ 0`, with `x_o(0) > 0`, and for every `t ≥ 0` and `i ∈ ι`,
the `i`-th component of the [Lotka–Volterra trajectory](lv-trajectory.md) `Y` has derivative
`F_i(Y(τ(t)))` at the time `τ(t)`, where `τ` is the [Lotka–Volterra time](time-change.md) and `F`
the [Lotka–Volterra field](lv-field.md) with the [growth rates](lv-growth.md) and
[interaction matrix](lv-interaction.md) of `A`. So `Y` solves the Lotka–Volterra equation at every
time of the image of `[0, ∞)` under `τ`.
