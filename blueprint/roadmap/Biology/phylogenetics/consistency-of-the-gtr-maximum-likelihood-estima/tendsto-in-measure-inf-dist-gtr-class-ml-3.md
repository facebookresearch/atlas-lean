# The chosen GTR pair-site MLE converges in probability to the class

Let `Θ` be a nonempty compact metric space. Let `ι` be a finite set of states and let `π`, `s` and
`t` give each parameter `θ` base frequencies `π θ : ι → ℝ`, exchangeabilities `s θ` (a real `ι × ι`
matrix) and a branch length `t θ > 0`, with every `(π θ, s θ)` in the
[GTR parameter domain](../identifiability-of-the-gtr-model/is-gtrparam.md): `π θ i > 0`,
`∑_i π θ i = 1`, `s θ` symmetric and `s θ i j > 0` for `i ≠ j`. Write `law θ` for the
[pair-site law](gtr-law.md) of `θ`, assumed continuous in `θ`, and `C` for the
[identified class](gtr-class.md) of `θ₀`: the parameters `θ` with `π θ = π θ₀` and
`t θ · s θ i j = t θ₀ · s θ₀ i j` for all `i ≠ j`. Let every subset of `ι × ι` be measurable. Let
`P` be a finite measure on `Ω` and let the columns `X 0, X 1, …` be measurable maps `Ω → ι × ι` that
are pairwise independent and identically distributed under `P`, with `P (X 0 = a) = law θ₀ a` for
every pattern `a`. Then the [chosen maximum-likelihood estimate](mle.md) `est n ω` of the pair-site
model for the
[empirical site-pattern frequencies](../consistency-of-minimum-distance-gtr-estimators/empirical-freq.md)
of the columns satisfies, for every `ε > 0`, `P {ω : d(est n ω, C) ≥ ε} → 0` as `n → ∞`, where
`d(θ, C) = inf_{θ' ∈ C} d(θ, θ')`. The estimator need not be measurable: `P` of a set that is not
measurable is its outer measure. Summing the sampling equalities over the finitely many patterns
gives `P(Ω) = ∑_a law θ₀ a = 1`, as the [pair-site law sums to one](sum-gtr-law.md), so this is
consistency in probability.
