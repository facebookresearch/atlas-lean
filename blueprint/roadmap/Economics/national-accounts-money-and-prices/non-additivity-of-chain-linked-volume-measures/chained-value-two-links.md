# Two-link chained real value of a basket

The chained real value of a basket over two links is its period-0 nominal value
times the chained index of its period-0-to-1 Laspeyres volume growth (period-0
prices) and its period-1-to-2 Laspeyres volume growth (period-1 prices):
`(∑_i p₀(i) * q₀(i)) * g₁ * g₂`, where
`g₁ = (∑_i p₀(i) * q₁(i)) / (∑_i p₀(i) * q₀(i))` and
`g₂ = (∑_i p₁(i) * q₂(i)) / (∑_i p₁(i) * q₁(i))`, with the convention `x / 0 = 0`.
