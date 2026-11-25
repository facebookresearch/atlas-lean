# The log-likelihood criterion is uniformly Lipschitz in the frequencies

Let `Θ` be a compact topological space, `σ` a finite set and `law : Θ → (σ → ℝ)` continuous with
`law θ a > 0` for all `θ` and `a`. There is a constant `C ≥ 0` such that the
[log-likelihood criterion](log-lik.md) satisfies `|L(f, θ) - L(g, θ)| ≤ C · d(f, g)` for all
frequencies `f, g : σ → ℝ` and all `θ ∈ Θ`, where `d(f, g) = max_a |f a - g a|` is the sup distance
(`0` when `σ` is empty).
