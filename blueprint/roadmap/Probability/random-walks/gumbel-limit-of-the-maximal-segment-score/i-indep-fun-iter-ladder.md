# Excursion functionals on the canonical path space are i.i.d.

Let `ν` be a probability measure on `ℝ`, `P = ν^ℕ` the product measure on paths `ℕ → ℝ`, `β` a
measurable space and `φ` a measurable map from paths to `β`. Suppose `φ` is determined by the scores
before the [first descending ladder epoch](desc-ladder-epoch.md): for every `t` and every measurable
`B ⊆ β`, the paths with [descent](has-desc-ladder.md) at `τ₋ = t` and `φ ∈ B` form a set in the
[σ-algebra of the first `t` scores](past-measurable-space.md). Suppose also that `P`-almost every
walk drops below `0`. Then the values `φ_i` of `φ` [on the successive excursions](iter-ladder.md)
are independent under `P`, and each has the law of `φ`.
