# Replicator to Lotka–Volterra, infinitesimally

For a finite set `ι`, a payoff matrix `A` on the strategies `ι ∪ {o}`, a curve `x` and a time `t`,
suppose every `x_k` has derivative `x_k(t) ((A x(t))_k - f̄(x(t)))` at `t`, the replicator equation
of the game with [mean fitness](../replicator-dynamics/mean-fitness.md) `f̄(x) = ∑_k x_k (A x)_k`,
and `x_o(t) ≠ 0`. Then the [Lotka–Volterra coordinates](to-lv.md) `y = (x_i / x_o)_i` have
derivative `x_o(t) F(y(t))` at `t`, where `F` is the [Lotka–Volterra field](lv-field.md) with the
[growth rates](lv-growth.md) and [interaction matrix](lv-interaction.md) of `A`.
