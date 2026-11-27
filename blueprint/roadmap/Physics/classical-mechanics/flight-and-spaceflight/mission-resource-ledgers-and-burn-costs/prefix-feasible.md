# Prefix feasibility of a resource schedule

For a type `ι` of resources, floors `lo` and capacities `hi : ι → ℝ`, nonnegative reserves
`r : ι → [0, ∞)`, initial stocks `s₀ : ι → ℝ`, signed flows `flow : ι → ℕ → ℝ` and a horizon
`N ∈ ℕ`, the schedule is prefix feasible if `lo i + r i ≤ stock(i, t) ≤ hi i` for every resource `i`
and every `t ≤ N`, the start `t = 0` and the end `t = N` included, where
`stock(i, t) = s₀ i + ∑_{k < t} flow i k` is the [stock](stock.md). The reserve is deducted once, in
the lower bound, and is not also a scheduled flow; since it is nonnegative, a feasible schedule
[never goes below the floor](lo-le-stock.md) at a prefix `t ≤ N`.
