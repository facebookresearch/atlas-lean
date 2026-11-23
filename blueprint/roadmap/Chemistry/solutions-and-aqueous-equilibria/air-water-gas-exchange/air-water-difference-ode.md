# Air water difference ode

The disequilibrium `d t = H * p t - c t` satisfies the linear equation
`d' t = -rate * d t` with `rate = k * A * (H * R * T / Vg + 1 / Vw)`.
The identity holds for all real `k`, `A`, `H`, `R`, `T`; it describes
relaxation toward equilibrium only when `rate > 0` (see
`air_water_rate_pos`).
