# The newest pipeline entry is the latest order

In the backlogging inventory model with lead time `L ∈ ℕ`, initial pipeline quantities
`a_0, …, a_{L-1} ≥ 0` (arriving in periods `0, …, L - 1`), orders `q_t ≥ 0` placed in period `t`
(arriving `L` periods later), demands `d_t ≥ 0` and initial net stock `I₀ ∈ ℝ`, if `L > 0` then the
last coordinate (`j = L - 1`) of the pipeline at period `t + 1` is the order `q_t` placed in period
`t`. Together with the forward shift of the other coordinates, the new pipeline is the old pipeline
without its head, followed by `q_t`.
