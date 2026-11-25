# Under full identifiability the MLE converges almost surely

Let `Θ` be a compact metric space, `σ` a finite set of site patterns, every subset of which is
measurable, and `law : Θ → (σ → ℝ)` continuous, positive and normalized: `law θ a > 0` for all `θ`
and `a`, and `∑_a law θ a = 1` for every `θ`. Let `θ₀ ∈ Θ` be such that every `θ` with
`law θ = law θ₀` is `θ₀`. Let `P` be a finite measure on `Ω` and let the columns `X 0, X 1, …` be
measurable maps `Ω → σ` that are pairwise independent and identically distributed under `P`, with
`P (X 0 = a) = law θ₀ a` for every pattern `a`. Then every [maximum-likelihood estimator](is-mle.md)
`est` for the
[empirical site-pattern frequencies](../consistency-of-minimum-distance-gtr-estimators/empirical-freq.md)
of the columns satisfies `est n ω → θ₀` as `n → ∞` for `P`-almost every `ω`: the analogue of Chang's
Lemma 5.1, under the positivity of the model. Summing the sampling equalities over the finitely many
patterns gives `P(Ω) = ∑_a law θ₀ a = 1`, so `P` is a probability measure.
