# Period-by-period simulation of the inventory system

In the backlogging inventory model with lead time `L ∈ ℕ`, initial pipeline quantities
`a_0, …, a_{L-1} ≥ 0` (arriving in periods `0, …, L - 1`), orders `q_t ≥ 0` placed in period `t`
(arriving `L` periods later), demands `d_t ≥ 0` and initial net stock `I₀ ∈ ℝ`, the simulation
applies the one-period transition for `H` periods from the state `(I₀, a)`, using the order `q_H`
and demand `d_H` at step `H`: `x_0 = (I₀, a)` and `x_{H+1} = step(x_H, q_H, d_H)`. No stock cap or
action saturation is applied; the state carries the pipeline as well as the stock.
