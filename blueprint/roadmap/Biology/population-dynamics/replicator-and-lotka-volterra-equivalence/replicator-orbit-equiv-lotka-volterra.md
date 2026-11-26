# Orbital equivalence, replicator to Lotka–Volterra

Let `ι` be a finite nonempty set, so that the strategies `ι ∪ {o}` number at least two, `A` a
payoff matrix on them, and `x` a [solution](../replicator-dynamics/is-solution.md) of the replicator
equation of the game, `x_k' = x_k ((A x)_k - f̄(x))` for `t ≥ 0`, starting in the interior of the
simplex: every `x_k(0) > 0` and `∑_k x_k(0) = 1`. Then, with `τ` the
[Lotka–Volterra time](time-change.md) and `Y` the [Lotka–Volterra trajectory](lv-trajectory.md)
(Hofbauer and Sigmund 1998, §7.5):

- `τ(0) = 0`, `τ` is continuously differentiable on `ℝ`, and its derivative at every real `t` is
  `x_o(max(t, 0)) > 0`, so `τ` preserves orientation;
- for every `t ≥ 0` and `i ∈ ι`, `Y_i(τ(t)) = x_i(t) / x_o(t) > 0`, and `Y_i` has derivative
  `F_i(Y(τ(t)))` at `τ(t)`, where `F` is the [Lotka–Volterra field](lv-field.md) with the
  [growth rates](lv-growth.md) and [interaction matrix](lv-interaction.md) of `A`;
- `τ(t) < t` for every `t > 0`: the original times are not identified.

All states involved have positive coordinates; boundary states are excluded.
