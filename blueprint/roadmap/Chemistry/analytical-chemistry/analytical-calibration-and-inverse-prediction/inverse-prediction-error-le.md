# Error bound for inverse prediction with perturbed parameters

Let `a`, `b`, `x`, `y` and `e` be real numbers with `y = b x + a + e`: an observation of the
calibration line with intercept `a`, slope `b`, input `x` and observation error `e`. Let `X`, `E`,
`D_a` and `D_b` be nonnegative bounds with `|x| ≤ X`, `|e| ≤ E` and `D_b < |b|`, and let the
perturbations `d_a` and `d_b` of the intercept and the slope satisfy `|d_a| ≤ D_a` and
`|d_b| ≤ D_b`. Then the [inverse prediction](inverse-prediction.md) `x̂ = (y − a) / b` with the
perturbed parameters `a + d_a` and `b + d_b` satisfies

`|(y − a − d_a) / (b + d_b) − x| ≤ (D_b X + D_a + E) / (|b| − D_b)`.

Since `|d_b| ≤ D_b < |b|`, the perturbed slope `b + d_b` is nonzero.
