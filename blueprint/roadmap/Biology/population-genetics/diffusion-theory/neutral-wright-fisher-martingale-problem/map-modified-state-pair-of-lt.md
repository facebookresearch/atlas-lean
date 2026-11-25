# The two-time law of the realization at times s < t

For every `x ∈ [0, 1]` and all times `0 ≤ s < t`, the joint law of `(X_s, X_t)` under the
[canonical path measure](../construction-of-the-neutral-wright-fisher-diffus/raw-measure.md) `P_x`,
where `X` is the
[continuous realization](../construction-of-the-neutral-wright-fisher-diffus/modified-process.md)
started at `x`, is `K_s(x, ·) ⊗ K_{t - s}`, with `K` the
[neutral Wright–Fisher kernel](../construction-of-the-neutral-wright-fisher-diffus/neutral-kernel.md):
`P_x(X_s ∈ A, X_t ∈ B) = ∫_A K_{t - s}(y, B) K_s(x, dy)` for measurable `A, B ⊆ [0, 1]`.
