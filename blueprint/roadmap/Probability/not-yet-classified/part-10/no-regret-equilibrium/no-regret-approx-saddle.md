# No-regret dynamics give approximate saddle points

In the matrix game `A` (row player
maximizes `u(p, q) = p.weights ⬝ᵥ (A *ᵥ q.weights)`), suppose the row player's average regret
`(1/T) ∑ₜ u(x, q t) - (1/T) ∑ₜ u(p t, q t)` is at most `εrow` for every mixed strategy `x` and the
column player's average regret `(1/T) ∑ₜ u(p t, q t) - (1/T) ∑ₜ u(p t, y)` is at most `εcol` for
every mixed strategy `y`. Then the average strategies `p̄ = avgStrategy hT p` and
`q̄ = avgStrategy hT q` satisfy `u(x, q̄) - u(p̄, y) ≤ εrow + εcol` for all `x` and `y`.
