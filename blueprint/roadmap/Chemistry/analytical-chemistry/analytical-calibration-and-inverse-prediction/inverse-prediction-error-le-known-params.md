# Error bound for inverse prediction with exact parameters

Let `a`, `x`, `e`, `y` and `E` be real numbers and `b ≠ 0`, with `y = b x + a + e`, `E ≥ 0` and
`|e| ≤ E`. Then the [inverse prediction](inverse-prediction.md) `x̂ = (y − a) / b` satisfies

`|(y − a) / b − x| ≤ E / |b|`.

No bound on the input `x` is needed. It is the case `D_a = D_b = 0` of the
[bound with perturbed parameters](inverse-prediction-error-le.md).
