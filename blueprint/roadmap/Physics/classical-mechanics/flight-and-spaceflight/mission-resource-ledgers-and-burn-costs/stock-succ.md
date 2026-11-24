# Each step adds its signed flow to the stock

For all initial stocks `s₀`, flows `flow`, resources `i` and `t ∈ ℕ`, the [stock](stock.md)
`stock(i, t) = s₀ i + ∑_{k < t} flow i k` satisfies `stock(i, t + 1) = stock(i, t) + flow i t`.
