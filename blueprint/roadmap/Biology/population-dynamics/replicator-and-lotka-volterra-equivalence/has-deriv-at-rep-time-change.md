# Derivative of the replicator time change

For a finite set `ι`, a payoff matrix `A` on the strategies `ι ∪ {o}` and a curve `y` such that
every `y_i` has derivative `F_i(y(τ))` at every `τ ≥ 0`, where `F` is the
[Lotka–Volterra field](lv-field.md) with the [growth rates](lv-growth.md) and
[interaction matrix](lv-interaction.md) of `A`, the [replicator time](rep-time-change.md) `t(·)`
has derivative `1 + ∑_j y_j(max(τ, 0))` at every real `τ`.
