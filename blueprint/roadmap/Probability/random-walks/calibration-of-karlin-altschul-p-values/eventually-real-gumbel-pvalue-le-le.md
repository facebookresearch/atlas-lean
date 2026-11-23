# Asymptotic validity from the Gumbel lower bound

Let `P` be a probability measure on `Ω`, `M n : Ω → ℝ` measurable statistics for `n = 0, 1, …`,
`K > 0` and `θ > 0`. Suppose the Gumbel lower bound
`liminf_n P(M n ≤ log n / θ + x) ≥ exp(-K e^{-θ x})` for every real `x`, that is, for every
`ε > 0`, eventually `P(M n ≤ log n / θ + x) ≥ exp(-K e^{-θ x}) - ε`. Then for every level
`α ∈ [0, 1]` and every `ε > 0`, eventually `P(pₙ ≤ α) ≤ α + ε`, where
`pₙ = 1 - exp(-K n e^{-θ M n})` is the [Karlin–Altschul p-value](gumbel-pvalue.md) of `M n`;
equivalently `limsup_n P(pₙ ≤ α) ≤ α`.
