# Almost-sure point consistency for a singleton GTR class

Let `Θ` be a compact metric space. Let `ι` be a finite set of states and let `π`, `s` and `t` give
each parameter `θ` base frequencies `π θ : ι → ℝ`, exchangeabilities `s θ` (a real `ι × ι` matrix)
and a branch length `t θ > 0`, with every `(π θ, s θ)` in the
[GTR parameter domain](../gtr-identifiability-and-estimation/identifiability-of-the-gtr-model/is-gtrparam.md): `π θ i > 0`,
`∑_i π θ i = 1`, `s θ` symmetric and `s θ i j > 0` for `i ≠ j`. Write `law θ` for the
[pair-site law](gtr-law.md) of `θ`, assumed continuous in `θ`, and `C` for the
[identified class](gtr-class.md) of `θ₀`: the parameters `θ` with `π θ = π θ₀` and
`t θ · s θ i j = t θ₀ · s θ₀ i j` for all `i ≠ j`. Suppose `C = {θ₀}`: no other parameter has the
base frequencies and the off-diagonal products `t θ · s θ i j` of `θ₀`, as with a known branch
length and a parametrization injective in `(π, s)` off the diagonal. Let every subset of `ι × ι` be
measurable. Let `P` be a finite measure on `Ω` and let the columns `X 0, X 1, …` be measurable maps
`Ω → ι × ι` that are pairwise independent and identically distributed under `P`, with
`P (X 0 = a) = law θ₀ a` for every pattern `a`. Then every [maximum-likelihood estimator](is-mle.md)
`est` for the pair-site model and the
[empirical site-pattern frequencies](../consistency-of-minimum-distance-gtr-estimators/empirical-freq.md)
of the columns satisfies `est n ω → θ₀` as `n → ∞` for `P`-almost every `ω`. Summing the sampling
equalities over the finitely many patterns gives `P(Ω) = ∑_a law θ₀ a = 1`, as the
[pair-site law sums to one](sum-gtr-law.md), so `P` is a probability measure.
