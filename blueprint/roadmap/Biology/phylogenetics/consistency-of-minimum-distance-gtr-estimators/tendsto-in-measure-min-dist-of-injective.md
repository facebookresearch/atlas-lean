# Under full identifiability the minimum-distance estimates converge

Let `Θ` be a compact metric space, `σ` a finite set of site patterns, every subset of which is
measurable, and `law : Θ → (σ → ℝ)` continuous. Let `θ₀ ∈ Θ` be such that every `θ` with
`law θ = law θ₀` is `θ₀`. Let `P` be a finite measure on `Ω` and let the columns `X 0, X 1, …` be
measurable maps `Ω → σ` that are pairwise independent and identically distributed under `P`, with
`P (X 0 = a) = law θ₀ a` for every pattern `a`. Then every
[minimum-distance estimator](is-min-dist-estimator.md) `est` for the
[empirical site-pattern frequencies](empirical-freq.md) of the columns converges to `θ₀` in
`P`-measure: for every `ε > 0`, `P {ω : d(est n ω, θ₀) ≥ ε} → 0` as `n → ∞`. The estimator need not
be measurable: `P` of a set that is not measurable is its outer measure. Pairwise independence
forces the total mass of `P` to be `0` or `1`, so this is convergence in probability unless `P` is
zero.
