# Closed form of the outstanding pipeline total

In the backlogging inventory model with lead time `L ∈ ℕ`, initial pipeline quantities
`a_0, …, a_{L-1} ≥ 0` (arriving in periods `0, …, L - 1`), orders `q_t ≥ 0` placed in period `t`
(arriving `L` periods later), demands `d_t ≥ 0` and initial net stock `I₀ ∈ ℝ`, the total
outstanding pipeline quantity at period `H` is
`P_H = ∑_{j < L, j ≥ H} a_j + ∑_{max(0, H - L) ≤ t < H} q_t`: the initial quantities not yet
received plus the orders placed in the last `L` periods before `H`. For `L = 0` the second sum is
empty.
