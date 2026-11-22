# Later receipts are orders placed one lead time earlier

In the backlogging inventory model with lead time `L ∈ ℕ`, initial pipeline quantities
`a_0, …, a_{L-1} ≥ 0` (arriving in periods `0, …, L - 1`), orders `q_t ≥ 0` placed in period `t`
(arriving `L` periods later), demands `d_t ≥ 0` and initial net stock `I₀ ∈ ℝ`, if `t ≥ L` then the
receipt of period `t` is the order placed in period `t - L`: `r_t = q_{t-L}`.
