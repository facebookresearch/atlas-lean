# Mean Vec

The coordinate-wise finite mean of a random vector `X : Ω → Fin n → ℝ`: coordinate `i`
is the expectation `FiniteProbability.expectation p (X · i)`. For a finite distribution
(`0 ≤ p`, `∑ ω, p ω = 1`) this is the mean vector of `X`; the distribution conditions are
hypotheses of the lemmas below, not part of the definition.
