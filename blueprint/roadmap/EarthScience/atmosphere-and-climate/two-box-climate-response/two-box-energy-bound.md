# Exponential energy bound for the unit two-box model

Suppose `Ts` and `Td` are differentiable at every time `t`, with
`Ts'(t) = 1 - Ts(t) - (Ts(t) - Td(t))` and `Td'(t) = Ts(t) - Td(t)`, and start from
`Ts(0) = Td(0) = 0`, so that the energy `E(t) = ((Ts(t) - 1)² + (Td(t) - 1)²) / 2` has
`E(0) = 1`. Then `E(t) ≤ exp(-(2/3) t) = E(0) exp(-(2/3) t)` for every `t ≥ 0`. This is the
exponential anomaly-energy bound with unit parameters, `xs = Ts - 1`, `xd = Td - 1` and
`c = min(2/3, 1) = 2/3`.
