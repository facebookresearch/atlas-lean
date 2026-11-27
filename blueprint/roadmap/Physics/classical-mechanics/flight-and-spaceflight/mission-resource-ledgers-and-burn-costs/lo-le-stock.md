# A prefix-feasible schedule never takes a stock below its floor up to N

For a type `ι` of resources, floors `lo` and capacities `hi : ι → ℝ`, nonnegative reserves
`r : ι → [0, ∞)`, initial stocks `s₀ : ι → ℝ`, signed flows `flow : ι → ℕ → ℝ` and a horizon
`N ∈ ℕ`, if the schedule is [prefix feasible](prefix-feasible.md) over the horizon `N`, then
`lo i ≤ stock(i, t)` for every resource `i` and every `t ≤ N`, because the reserve is nonnegative;
here `stock(i, t) = s₀ i + ∑_{k < t} flow i k` is the [stock](stock.md).
