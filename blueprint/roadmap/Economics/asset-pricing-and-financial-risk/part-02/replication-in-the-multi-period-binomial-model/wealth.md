# Wealth of a self-financing strategy in the binomial tree

Given real initial capital `x₀`, a gross riskless return `R` and a strategy `δ` that holds
`δ(s)` shares over the period following each history `s`, the wealth is defined along every
history of moves: it is `x₀` at the root, and one further move `b` after `s` gives
`X(s, b) = δ(s) * S(s, b) + R * (X(s) - δ(s) * S(s))`, where `S` is the binomial stock price
(initial price `S₀`, move factors `u` and `d`). In time notation,
`X_{t+1} = δ_t S_{t+1} + R (X_t - δ_t S_t)`: the shares are revalued at the new price and the
rest of the wealth earns the riskless return.
