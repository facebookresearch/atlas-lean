# Simulation advances by one transition step

In the backlogging inventory model with lead time `L ∈ ℕ`, initial pipeline quantities
`a_0, …, a_{L-1} ≥ 0` (arriving in periods `0, …, L - 1`), orders `q_t ≥ 0` placed in period `t`
(arriving `L` periods later), demands `d_t ≥ 0` and initial net stock `I₀ ∈ ℝ`, the simulation
advances by one transition step: `x_{H+1} = step(x_H, q_H, d_H)` for every `H`, the transition using
the order and demand of period `H`.
