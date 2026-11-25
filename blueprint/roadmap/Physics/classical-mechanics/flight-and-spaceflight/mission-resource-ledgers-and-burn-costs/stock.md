# Stock of a resource after the first t steps

For a type `ι` of resources, initial stocks `s₀ : ι → ℝ`, signed flows `flow : ι → ℕ → ℝ`, a
resource `i` and `t ∈ ℕ`, `stock(i, t) = s₀ i + ∑_{k < t} flow i k`: the initial stock plus the
signed flows of steps `0, …, t − 1`. Positive flows add to the stock and negative flows draw from
it; each resource keeps its own units.
