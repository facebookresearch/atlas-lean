# Strong Markov property of Cramér scores at the ladder epoch

Let `X 0, X 1, …` be scores on `(Ω, P)` satisfying the [Cramér conditions](cramer-scores.md), and
`E` a measurable set of paths such that, for every `t`, the paths in `E` whose walk
[drops below `0`](has-desc-ladder.md) with [first descending ladder epoch](desc-ladder-epoch.md)
`τ₋ = t` form a set in the [σ-algebra of the first `t` scores](past-measurable-space.md). Then for
every measurable set `B` of paths, `P(X ∈ E and X' ∈ B) = P(X ∈ E) P(X ∈ B)`, where `X` is the
score path and `X' = (X (τ₋ + j))_j` the path restarted at `τ₋`: the restarted path is independent
of `{X ∈ E}` and has the law of the original path.
