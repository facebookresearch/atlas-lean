# Lotka–Volterra to replicator, infinitesimally

For a finite set `ι`, a payoff matrix `A` on the strategies `ι ∪ {o}`, a curve `y : ℝ → (ι → ℝ)`
and a time `τ`, suppose every `y_i` has derivative `F_i(y(τ))` at `τ`, where `F` is the
[Lotka–Volterra field](lv-field.md) with the [growth rates](lv-growth.md) and
[interaction matrix](lv-interaction.md) of `A`, and `S(τ) = 1 + ∑_j y_j(τ) ≠ 0`. Then the
[replicator coordinates](of-lv.md) `x = (1, y) / S` have, for every strategy `k`, derivative
`S(τ) x_k(τ) ((A x(τ))_k - f̄(x(τ)))` at `τ`, where `f̄(x) = ∑_k x_k (A x)_k` is the
[mean fitness](../replicator-dynamics/mean-fitness.md): `S(τ)` times the replicator field.
