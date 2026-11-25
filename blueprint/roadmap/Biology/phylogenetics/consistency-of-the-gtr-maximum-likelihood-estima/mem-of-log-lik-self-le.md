# Maximizers of the expected log-likelihood lie in the identified class

Let `σ` be a finite set and `law` a map from a set `Θ` to the functions `σ → ℝ` that is positive and
normalized: `law θ a > 0` for all `θ` and `a`, and `∑_a law θ a = 1` for every `θ`. Let `θ₀` be
identified up to a set `E ⊆ Θ`: every `θ` with `law θ = law θ₀` lies in `E`. Then every `θ` at which
the expected log-likelihood under `law θ₀` is at least its value at `θ₀`,
`∑_a law θ₀ a · log (law θ a) ≥ ∑_a law θ₀ a · log (law θ₀ a)`, lies in `E`.
