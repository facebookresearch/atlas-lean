# Conservation of stock plus pipeline

In the backlogging inventory model with lead time `L ∈ ℕ`, initial pipeline quantities
`a_0, …, a_{L-1} ≥ 0` (arriving in periods `0, …, L - 1`), orders `q_t ≥ 0` placed in period `t`
(arriving `L` periods later), demands `d_t ≥ 0` and initial net stock `I₀ ∈ ℝ`, where the receipt of
period `t` is `r_t = a_t` if `t < L` and `r_t = q_{t-L}` otherwise, the net stock is `I_0 = I₀`,
`I_{t+1} = I_t + r_t - d_t` and `P_H = ∑_{j < L} r_{H+j}` is the outstanding pipeline total, for
every horizon `H` (whether `H` is `0`, below, equal to or above `L`):
`I_H + P_H = I₀ + ∑_{j < L} a_j + ∑_{t < H} q_t - ∑_{t < H} d_t`. Every outstanding order is
retained at the horizon.
