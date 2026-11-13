# Sample Mean fin eq sum range div

The canonical sample mean `FiniteProbability.sampleMean` of the first `n` observations
`X 0 ω, …, X (n - 1) ω` is `(∑ i ∈ range n, X i ω) / n`, the form used by Mathlib's strong law
`ProbabilityTheory.strong_law_ae_real`. For `n = 0` both sides are `0`.
