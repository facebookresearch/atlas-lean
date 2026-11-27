# Later pipeline entries come from placed orders

In the backlogging inventory model with lead time `L ∈ ℕ`, initial pipeline quantities
`a_0, …, a_{L-1} ≥ 0` (arriving in periods `0, …, L - 1`), orders `q_t ≥ 0` placed in period `t`
(arriving `L` periods later), demands `d_t ≥ 0` and initial net stock `I₀ ∈ ℝ`, if `j < L` and
`t + j ≥ L`, then coordinate `j` of the pipeline at period `t` is the already-placed order
`q_{t+j-L}`.
