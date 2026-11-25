# Uniform law of large numbers for the log-likelihood

Let `Θ` be a compact topological space, `σ` a finite set of site patterns, every subset of which is
measurable, and `law : Θ → (σ → ℝ)` continuous with `law θ a > 0` for all `θ` and `a`. Fix `θ₀ ∈ Θ`.
Let `P` be a finite measure on `Ω` and let the columns `X 0, X 1, …` be measurable maps `Ω → σ` that
are pairwise independent and identically distributed under `P`, with `P (X 0 = a) = law θ₀ a` for
every pattern `a`. Then for `P`-almost every `ω` the average log-likelihood `L(p̂ₙ(ω), θ)` at the
[empirical site-pattern frequencies](../consistency-of-minimum-distance-gtr-estimators/empirical-freq.md)
of the first `n` columns converges to the expected log-likelihood `L(law θ₀, θ)` uniformly in
`θ ∈ Θ`, where `L` is the [log-likelihood criterion](log-lik.md). Pairwise independence forces the
total mass of `P` to be `0` or `1`, so `P` is a probability measure unless it is zero.
