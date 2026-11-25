# Orbital equivalence, Lotka–Volterra to replicator

Let `ι` be a finite nonempty set of species, `A` a payoff matrix on the strategies `ι ∪ {o}`, and
`y` a positive solution on `[0, ∞)` of the Lotka–Volterra equation `y_i' = F_i(y)`, where `F` is the
[Lotka–Volterra field](lv-field.md) with the [growth rates](lv-growth.md) and
[interaction matrix](lv-interaction.md) of `A`: each `y_i` has derivative `F_i(y(τ))` and
`y_i(τ) > 0` at every `τ ≥ 0`. Then, with `t(·)` the [replicator time](rep-time-change.md) and `X`
the [replicator trajectory](rep-trajectory.md) (Hofbauer and Sigmund 1998, §7.5):

- `t(0) = 0`, `t(·)` is continuously differentiable on `ℝ`, and its derivative at every real `τ` is
  `1 + ∑_j y_j(max(τ, 0)) ≥ 1`, so it preserves orientation;
- `X` [solves the replicator equation](../replicator-dynamics/is-solution.md) of the game for all
  `t ≥ 0`, and `X(t(τ))` is the [replicator coordinate vector](of-lv.md) of `y(τ)` for every
  `τ ≥ 0`;
- for every `t ≥ 0`, `X(t)` lies in the interior of the simplex: every coordinate is positive and
  they sum to `1`;
- `τ < t(τ)` for every `τ > 0`: the original times are not identified.

Only Lotka–Volterra solutions that exist and stay positive for all `τ ≥ 0` are covered; boundary
states are excluded.
