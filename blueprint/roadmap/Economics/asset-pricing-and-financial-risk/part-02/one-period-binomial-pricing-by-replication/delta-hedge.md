# Delta-hedge stock holding for a one-step claim

The delta hedge of the one-step claim paying `Cu` in the up state and `Cd` in the down state,
for a stock worth `S₀` today and `u * S₀` or `d * S₀` at expiry, is the share holding
`Δ = (Cu - Cd) / ((u - d) * S₀)`, defined for all real values with the convention x / 0 = 0
(`Δ = 0` when `u = d` or `S₀ = 0`). When `S₀ ≠ 0`, `u ≠ d` and `R ≠ 0`, together with the bond
holding `B = (u * Cd - d * Cu) / ((u - d) * R)` (bond price `1` today, `R` at expiry) it makes
the portfolio payoff match the claim in both states.
