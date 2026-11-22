# Bond position of the one-step replicating portfolio

The bond holding of the one-step replicating portfolio for a claim paying `Cu` in the up state
and `Cd` in the down state (bond price `1` today and `R` at expiry) is
`B = (u * Cd - d * Cu) / ((u - d) * R)`, defined for all real values with the convention
x / 0 = 0 (`B = 0` when `u = d` or `R = 0`). When `S₀ ≠ 0`, `u ≠ d` and `R ≠ 0`, with the delta
hedge `Δ = (Cu - Cd) / ((u - d) * S₀)` it gives `Δ * (u * S₀) + B * R = Cu` and
`Δ * (d * S₀) + B * R = Cd`.
