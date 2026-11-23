# The chosen MLE converges in probability to the identified class

Let `Θ` be a nonempty compact metric space, `σ` a finite set of site patterns, every subset of which
is measurable, and `law : Θ → (σ → ℝ)` continuous, positive and normalized: `law θ a > 0` for all
`θ` and `a`, and `∑_a law θ a = 1` for every `θ`. Let `θ₀` be identified up to a set `E ⊆ Θ`: every
`θ` with `law θ = law θ₀` lies in `E`. Let `P` be a finite measure on `Ω` and let the columns
`X 0, X 1, …` be measurable maps `Ω → σ` that are pairwise independent and identically distributed
under `P`, with `P (X 0 = a) = law θ₀ a` for every pattern `a`. Then the
[chosen maximum-likelihood estimate](mle.md) `est n ω` for the
[empirical site-pattern frequencies](../consistency-of-minimum-distance-gtr-estimators/empirical-freq.md)
of the columns satisfies, for every `ε > 0`, `P {ω : d(est n ω, E) ≥ ε} → 0` as `n → ∞`, where
`d(θ, E) = inf_{θ' ∈ E} d(θ, θ')`. The estimator need not be measurable: `P` of a set that is not
measurable is its outer measure. Summing the sampling equalities over the finitely many patterns
gives `P(Ω) = ∑_a law θ₀ a = 1`, so this is consistency in probability.
