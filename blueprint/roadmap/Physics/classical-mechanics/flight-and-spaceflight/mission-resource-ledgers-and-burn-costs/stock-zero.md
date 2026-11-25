# Before any step the stock is the initial stock

For all initial stocks `s₀`, flows `flow` and resources `i`, the [stock](stock.md)
`stock(i, t) = s₀ i + ∑_{k < t} flow i k` satisfies `stock(i, 0) = s₀ i`.
