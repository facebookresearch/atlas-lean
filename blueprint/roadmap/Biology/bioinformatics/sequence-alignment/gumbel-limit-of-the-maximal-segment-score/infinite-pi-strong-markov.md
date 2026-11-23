# Strong Markov property of the i.i.d. path at the ladder epoch

Let `ν` be a probability measure on `ℝ`, `P = ν^ℕ` the product measure on paths `ℕ → ℝ`, and `E` a
set of paths such that, for every `t`, the paths in `E` whose walk
[drops below `0`](has-desc-ladder.md) with [first descending ladder epoch](desc-ladder-epoch.md)
`τ₋ = t` form a set in the [σ-algebra of the first `t` scores](past-measurable-space.md). Then for
every measurable set `B` of paths, `P(E ∩ D ∩ {x' ∈ B}) = P(E ∩ D) P(B)`, where `D` is the event
that the walk drops below `0` and `x'` is the [path seen from time](path-shift.md) `τ₋`: the on `D`
the restarted path is independent of `E` and has the law of the original path.
