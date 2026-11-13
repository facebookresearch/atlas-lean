# Expectation

The expectation `∑ x, p x * X x` of `X : α → ℝ` under a weight `p : α → ℝ` on a finite type
(MF06.1). For a finite distribution (`0 ≤ p`, `∑ x, p x = 1`) this is the mean of `X`. Mathlib's
`μ[X]` and ATLAS `PMF.expect` are Bochner integrals against a measure; this finite sum needs no
measurability or `ℝ≥0∞` conversion (`integral_toMeasure_eq_expectation` relates them). As a
function of `p` and `X` it is the dot product `p ⬝ᵥ X` (`expectation_eq_dotProduct`); the
separate name carries the probabilistic API.
