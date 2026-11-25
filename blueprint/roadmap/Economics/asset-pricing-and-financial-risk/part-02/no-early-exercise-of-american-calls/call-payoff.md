# Exercise payoff of a call on the binomial stock

The exercise payoff of a call with strike `K` at the node of the binomial tree reached by a
history `s` is `max(S(s) - K, 0)`, where the stock price there is
`S(s) = S₀ u^(number of up moves) d^(number of down moves)` (initial price `S₀`, up factor `u`,
down factor `d`; all parameters real).
