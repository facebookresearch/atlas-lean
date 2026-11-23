# Point consistency of the GTR pair-site MLE, in probability

Let `Θ` be a compact metric space. Let `ι` be a finite set of states and let `π`, `s` and `t` give
each parameter `θ` base frequencies `π θ : ι → ℝ`, exchangeabilities `s θ` (a real `ι × ι` matrix)
and a branch length `t θ > 0`, with every `(π θ, s θ)` in the
[GTR parameter domain](../identifiability-of-the-gtr-model/is-gtrparam.md): `π θ i > 0`,
`∑_i π θ i = 1`, `s θ` symmetric and `s θ i j > 0` for `i ≠ j`. Write `law θ` for the
[pair-site law](gtr-law.md) of `θ`, assumed continuous in `θ`, and `C` for the
[identified class](gtr-class.md) of `θ₀`: the parameters `θ` with `π θ = π θ₀` and
`t θ · s θ i j = t θ₀ · s θ₀ i j` for all `i ≠ j`. Suppose `C = {θ₀}`: no other parameter has the
base frequencies and the off-diagonal products `t θ · s θ i j` of `θ₀`. Let every subset of `ι × ι`
be measurable. Let `P` be a finite measure on `Ω` and let the columns `X 0, X 1, …` be measurable
maps `Ω → ι × ι` that are pairwise independent and identically distributed under `P`, with
`P (X 0 = a) = law θ₀ a` for every pattern `a`. Then every [maximum-likelihood estimator](is-mle.md)
`est` for the pair-site model and the
[empirical site-pattern frequencies](../consistency-of-minimum-distance-gtr-estimators/empirical-freq.md)
of the columns converges to `θ₀` in `P`-measure: for every `ε > 0`, `P {ω : d(est n ω, θ₀) ≥ ε} → 0`
as `n → ∞`. The estimator need not be measurable: `P` of a set that is not measurable is its outer
measure. Pairwise independence forces the total mass of `P` to be `0` or `1`, so this is convergence
in probability unless `P` is zero.
