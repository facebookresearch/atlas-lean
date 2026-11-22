# State-price vector and replication pricing

Under no arbitrage on
funded gains, `ψ = q / R` is strictly positive, sums to `1 / R`, and prices every
replicated payoff: the `ψ`-value of the payoff `∑ a, h a * X a ω` of portfolio `h`
equals its cost `∑ a, h a * p a`. The pricing probability `q` and its pricing
identity `∑ ω, q ω * X a ω = R * p a` are the ones supplied by `funded_ftap`.
