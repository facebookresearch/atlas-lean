# One-step arbitrage in the binomial model

The one-step bond/stock model has real parameters `S₀`, `u`, `d`, `R`, with no sign conditions
imposed: the bond costs `1` today and pays `R` at expiry; the stock costs `S₀` today and is worth
`u * S₀` in the up state and `d * S₀` in the down state. A portfolio of `Δ` shares of stock and
`B` units of the bond (any real numbers) costs `Δ * S₀ + B` today, pays `Δ * (u * S₀) + B * R`
in the up state and `Δ * (d * S₀) + B * R` in the down state. It is a one-step arbitrage, a
riskless profit, when its cost is at most `0`, both payoffs are at least `0`, and at least one
payoff is positive.
