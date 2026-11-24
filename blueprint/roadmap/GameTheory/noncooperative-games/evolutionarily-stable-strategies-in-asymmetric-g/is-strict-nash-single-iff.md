# Pure strict Nash equilibria

For finite sets `ι` and `κ`, payoff matrices `A : ι × κ → ℝ` and `B : κ × ι → ℝ`, and strategies
`i ∈ ι` and `k ∈ κ`, the pair of point masses at `i` and `k` is a
[strict Nash equilibrium](is-strict-nash.md) if and only if `A_jk < A_ik` for every `j ≠ i` and
`B_li < B_ki` for every `l ≠ k`: `i` is the unique best reply to `k` in role I and `k` the unique
best reply to `i` in role II.
