# The posterior mean is a convex shrinkage combination

For real `a`, `b > 0`, `s > 0` and `k ∈ ℕ`, `(a + k) / (b + s) = w · (k / s) + (1 − w) · (a / b)`
with the [shrinkage weight](shrinkage-weight.md) `w = s / (b + s) ∈ (0, 1)`. For `a > 0` the left
side is the [posterior mean](posterior-mean.md): the per-cell estimate `k / s` shrunk toward the
prior mean `a / b`.
