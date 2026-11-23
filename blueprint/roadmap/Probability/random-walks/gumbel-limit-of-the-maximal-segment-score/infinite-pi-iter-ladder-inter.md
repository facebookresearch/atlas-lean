# Joint law of excursion functionals on the canonical path space

Let `ν` be a probability measure on `ℝ`, `P = ν^ℕ` the product measure on paths `ℕ → ℝ`, `β` a
measurable space and `φ` a measurable map from paths to `β`. Suppose `φ` is determined by the scores
before the [first descending ladder epoch](desc-ladder-epoch.md): for every `t` and every measurable
`B ⊆ β`, the paths with [descent](has-desc-ladder.md) at `τ₋ = t` and `φ ∈ B` form a set in the
[σ-algebra of the first `t` scores](past-measurable-space.md). Suppose also that `P`-almost every
walk drops below `0`. Then for every `k` and measurable sets `B_0, B_1, …`,
`P(φ_i ∈ B_i for all i < k) = ∏_{i < k} P(φ ∈ B_i)`, where `φ_i` is `φ`
[evaluated on the `i`-th excursion](iter-ladder.md).
