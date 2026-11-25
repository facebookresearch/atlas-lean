# Change of measure on the first `n` observations, for laws with densities

Let `P₀` be a
probability measure on `X` and let each `Q i`, `i : ℕ`, be a probability measure on `X` with
`Q i = P₀.withDensity (f i)` for a measurable density `f i : X → ℝ≥0∞`. If the event `A` depends
only on the first `n` coordinates (it is measurable for `observationFiltration X n`), then
`(Measure.infinitePi Q)(A) = ∫_A ∏_{i<n} f i (ω i) dP₀^ℕ`. For instance, the law of the
observations with a change point, for `P₁ ≪ P₀`, has density `1` before the change and
`dP₁/dP₀` after it.
