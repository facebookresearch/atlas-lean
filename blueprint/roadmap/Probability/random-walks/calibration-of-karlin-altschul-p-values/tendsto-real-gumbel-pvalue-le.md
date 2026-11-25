# Exact asymptotic calibration from the Gumbel limit

Let `P` be a probability measure on `Ω`, `M n : Ω → ℝ` measurable statistics for `n = 0, 1, …`,
`K > 0` and `θ > 0`. Suppose the Gumbel limit `P(M n ≤ log n / θ + x) → exp(-K e^{-θ x})` as
`n → ∞`, for every real `x`. Then for every level `α ∈ [0, 1]`, `P(pₙ ≤ α) → α`, where
`pₙ = 1 - exp(-K n e^{-θ M n})` is the [Karlin–Altschul p-value](gumbel-pvalue.md) of `M n`.
