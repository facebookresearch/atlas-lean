# Minimum-distance estimators are consistent up to the identified class

Let `Θ` be a compact metric space of parameters, `σ` a finite set of site patterns, every subset of
which is measurable, and `law : Θ → (σ → ℝ)` continuous, the site-pattern law of the model. Let the
true parameter `θ₀` be identified up to a set `E ⊆ Θ`, for example its class under the permitted
symmetries: every `θ` with `law θ = law θ₀` lies in `E`. Let `P` be a finite measure on `Ω` and let
the columns `X 0, X 1, …` be measurable maps `Ω → σ` that are pairwise independent and identically
distributed under `P`, with `P (X 0 = a) = law θ₀ a` for every pattern `a`. Then every
[minimum-distance estimator](is-min-dist-estimator.md) `est` for the
[empirical site-pattern frequencies](empirical-freq.md) of the columns satisfies, for every `ε > 0`,
`P {ω : d(est n ω, E) ≥ ε} → 0` as `n → ∞`, where `d(θ, E) = inf_{θ' ∈ E} d(θ, θ')`. The estimator
need not be measurable: `P` of a set that is not measurable is its outer measure. Pairwise
independence forces the total mass of `P` to be `0` or `1`, so this is consistency in probability
unless `P` is zero.
