# Two box energy bound

Exponential energy bound: if `Ts, Td` satisfy the two-box ODE at
every `t` and start at `Ts 0 = Td 0 = 0` (so `E 0 = 1`), then for
`t ≥ 0`, `E t ≤ exp (-(2 / 3) * t)`, i.e.
`E t ≤ E 0 * exp (-(2 / 3) * t)`. This is the unit-parameter case of
`anomaly_energy_exp_bound` with `xs = Ts - 1`, `xd = Td - 1` and
`c = min (2 / 3) 1 = 2 / 3`.
