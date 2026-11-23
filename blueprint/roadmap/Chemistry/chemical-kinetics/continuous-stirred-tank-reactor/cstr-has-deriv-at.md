# Exponential relaxation at rate Q/V + k solves the reactor equation

Let `V > 0` be the reactor volume, `Q > 0` the flow, `k ≥ 0` the first-order rate constant, and
`c_in` and `c₀` real concentrations. With `c* = Q c_in / (Q + k V)`, the function
`c(t) = c* + (c₀ - c*) exp(-(Q/V + k) t)` satisfies `c'(t) = (Q/V) (c_in - c(t)) - k c(t)` at
every real `t`: it solves the continuous stirred-tank reactor equation
`V c' = Q (c_in - c) - k V c`.
