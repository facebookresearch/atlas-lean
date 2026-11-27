# Pipeline entries are scheduled receipts

In the backlogging inventory model with lead time `L ∈ ℕ`, initial pipeline quantities
`a_0, …, a_{L-1} ≥ 0` (arriving in periods `0, …, L - 1`), orders `q_t ≥ 0` placed in period `t`
(arriving `L` periods later), demands `d_t ≥ 0` and initial net stock `I₀ ∈ ℝ`, where the receipt of
period `t` is `r_t = a_t` if `t < L` and `r_t = q_{t-L}` otherwise, coordinate `j < L` of the
pipeline at period `t` is the receipt scheduled for period `t + j`: `r_{t+j}`.
