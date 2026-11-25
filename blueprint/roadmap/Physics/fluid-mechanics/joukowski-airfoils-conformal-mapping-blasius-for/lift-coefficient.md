# Lift coefficient L/(ρU²c/2) of a lift per unit span

For real `L`, `ρ`, `U` and `c`, the lift coefficient is `C_L = L/(ρU²c/2)`: the lift per unit span
`L` (for example a [signed lift](signed-lift.md)) divided by the dynamic pressure `ρU²/2` times the
chord `c`. With the convention that division by zero gives `0`, `C_L = 0` when `ρ = 0`, `U = 0` or
`c = 0`. The intended inputs are a density `ρ > 0`, a free-stream speed `U > 0` and a chord `c > 0`.
