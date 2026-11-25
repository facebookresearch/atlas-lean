# Information inequality, strict when the laws differ

Let `σ` be a finite set and `law` a map from a set `Θ` to the functions `σ → ℝ` that is positive and
normalized: `law θ a > 0` for all `θ` and `a`, and `∑_a law θ a = 1` for every `θ`. If
`law θ ≠ law θ₀`, the expected log-likelihood under `law θ₀` is strictly smaller at `θ` than at
`θ₀`: `∑_a law θ₀ a · log (law θ a) < ∑_a law θ₀ a · log (law θ₀ a)` (Newey and McFadden, Lemma
2.2).
