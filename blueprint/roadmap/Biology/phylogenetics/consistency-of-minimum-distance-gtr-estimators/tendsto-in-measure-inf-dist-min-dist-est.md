# The chosen minimizer is consistent up to the identified class

Let `Θ` be a nonempty compact metric space, `σ` a finite set of site patterns, every subset of which
is measurable, and `law : Θ → (σ → ℝ)` continuous. Let `θ₀ ∈ Θ` be identified up to a set `E ⊆ Θ`:
every `θ` with `law θ = law θ₀` lies in `E`. Let `P` be a finite measure on `Ω` and let the columns
`X 0, X 1, …` be measurable maps `Ω → σ` that are pairwise independent and identically distributed
under `P`, with `P (X 0 = a) = law θ₀ a` for every pattern `a`. Then the
[chosen minimum-distance estimate](min-dist-estimator.md) `est n ω` for the
[empirical site-pattern frequencies](empirical-freq.md) of the columns satisfies, for every `ε > 0`,
`P {ω : d(est n ω, E) ≥ ε} → 0` as `n → ∞`, where `d(θ, E) = inf_{θ' ∈ E} d(θ, θ')`. The estimator
need not be measurable: `P` of a set that is not measurable is its outer measure. Pairwise
independence forces the total mass of `P` to be `0` or `1`, so this is convergence in probability
unless `P` is zero.
