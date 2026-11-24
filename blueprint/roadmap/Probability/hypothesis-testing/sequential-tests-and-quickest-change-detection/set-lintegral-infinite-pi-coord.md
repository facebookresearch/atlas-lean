# Markov property of i.i.d. coordinates

Let `P₀` be a probability measure on `X`, let the
event `F` and the function `u : (ℕ → X) → ℝ≥0∞` be measurable for `observationFiltration X n`
(they depend only on the first `n` coordinates), and let `h : ℝ≥0∞ → X → ℝ≥0∞` be jointly
measurable. Then `∫_F h (u ω) (ω n) dP₀^ℕ = ∫_F ∫ h (u ω) x dP₀(x) dP₀^ℕ`: the next coordinate
`ω n` can be integrated out first.
