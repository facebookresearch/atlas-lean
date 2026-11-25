# A reserve in the floor is one deduction from the initial stock

For a type `ι` of resources, floors `lo` and capacities `hi : ι → ℝ`, nonnegative reserves
`r : ι → [0, ∞)`, initial stocks `s₀ : ι → ℝ`, signed flows `flow : ι → ℕ → ℝ` and a horizon
`N ∈ ℕ`, the schedule is [prefix feasible](prefix-feasible.md) with floors `lo`, capacities `hi`,
reserves `r` and initial stocks `s₀` if and only if it is prefix feasible with floors `lo`,
capacities `hi − r`, zero reserves and initial stocks `s₀ − r`.
