# Prefix feasibility includes the terminal check

For a type `ι` of resources, floors `lo` and capacities `hi : ι → ℝ`, nonnegative reserves
`r : ι → [0, ∞)`, initial stocks `s₀ : ι → ℝ`, signed flows `flow : ι → ℕ → ℝ` and a horizon
`N ∈ ℕ`, if the schedule is [prefix feasible](prefix-feasible.md) over the horizon `N`, then for
every resource `i`, `lo i + r i ≤ s₀ i + ∑_{k < N} flow i k ≤ hi i`.
