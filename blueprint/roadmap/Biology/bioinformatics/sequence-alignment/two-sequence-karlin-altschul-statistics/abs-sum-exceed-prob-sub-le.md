# Finite-size estimate of the expected number of exceeding diagonals

Let `p` and `q` be
[probability vectors](../../../../Probability/not-yet-classified/is-dist.md)
on a finite alphabet, `s` a real score on pairs of letters, `θ ≥ 0` a root of
`∑_{a, b} p_a q_b e^{θ s(a, b)} = 1` ([pair law](pair-law.md), [pair score](pair-score.md)), `K`
real, `ε ≥ 0`, `ℓ`, `m` and `n` natural numbers with `ℓ ≤ m` and `ℓ ≤ n`, and `t > 0`. Suppose
that for every natural number `L` with `ℓ ≤ L ≤ n`, the probability `P(M_L > t)` that the
[maximal segment score](../../../../Probability/random-walks/maximal-segment-score-of-a-random-sequence/max-seg-score.md) of `L`
independent letter pairs with the pair law, scored by the pair score, exceeds `t` satisfies
`|P(M_L > t) - K L e^{-θ t}| ≤ ε L e^{-θ t}`. Then the [exceedance probabilities](exceed-prob.md)
`p_d` of the diagonals of the `m × n` grid, over its [offsets](offsets.md) `-m < d < n`, satisfy
`|∑_d p_d - K m n e^{-θ t}| ≤ ε m n e^{-θ t} + 2 (1 + |K|) ℓ² e^{-θ t}`. The diagonals of length at
least `ℓ` use the assumed estimate, and the [at most `2 ℓ` shorter ones](card-filter-diag-len-lt-le.md)
the [exponential bound](exceed-prob-le.md) `p_d ≤ L e^{-θ t}` for a diagonal of length `L`.
