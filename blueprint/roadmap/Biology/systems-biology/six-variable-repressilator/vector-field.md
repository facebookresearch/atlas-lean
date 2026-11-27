# Right-hand side of the six-variable repressilator

For `n ∈ ℕ`, real `α` and `β`, and `x ∈ ℝ⁶`, write `mᵢ = xᵢ` and `pᵢ = x_{i+3}` for `i = 0, 1, 2`.
The six-variable field is

`m₀' = α / (1 + p₂ⁿ) − m₀`, `m₁' = α / (1 + p₀ⁿ) − m₁`, `m₂' = α / (1 + p₁ⁿ) − m₂`,
`pᵢ' = −β (pᵢ − mᵢ)`,

so gene `i` is repressed by the protein of gene `i − 1` (indices mod 3). With the convention
`x / 0 = 0`, a repression term is `0` when `pⱼⁿ = −1` (`n` odd and `pⱼ = −1`). This is the
Elowitz–Leibler mRNA–protein repressilator without leak; in the model the concentrations are
nonnegative, the maximal transcription rate `α` is positive and `β > 0` is the ratio of the protein
and mRNA decay rates.
