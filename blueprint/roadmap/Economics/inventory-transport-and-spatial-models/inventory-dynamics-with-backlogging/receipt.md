# Scheduled receipt in a period

In the backlogging inventory model with lead time `L ∈ ℕ`, initial pipeline quantities
`a_0, …, a_{L-1} ≥ 0` (arriving in periods `0, …, L - 1`), orders `q_t ≥ 0` placed in period `t`
(arriving `L` periods later), demands `d_t ≥ 0` and initial net stock `I₀ ∈ ℝ`, the scheduled
receipt of period `t` is `r_t = a_t` if `t < L`, and otherwise the order placed one lead time
earlier, `r_t = q_{t-L}`; for `L = 0` this is `q_t`. Event order per period: receive the scheduled
quantity, place an order, receive that new order immediately if `L = 0`, then serve demand.
