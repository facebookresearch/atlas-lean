# Post-dose amounts satisfy the affine recurrence

For all real `D`, `k` and `τ` and every natural number `n`, the amount just after dose `n + 1` is
the amount just after dose `n`, decayed by `exp (-k * τ)`, plus the new dose:
`P(n + 1) = exp (-k * τ) * P(n) + D`, where `P(n) = ∑_{i=0}^{n} D * exp (-k * (n * τ - i * τ))` is
the [post-dose amount](post-dose-amount.md).
