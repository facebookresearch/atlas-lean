# Post-dose closed form for the periodic trajectory

For all real `D`, `k` and `τ` and every natural number `n`, the
[amount just after dose](post-dose-amount.md) `n`,
`P(n) = ∑_{i=0}^{n} D * exp (-k * (n * τ - i * τ))`, is
`exp (-k * τ) ^ n * D + D * ∑_{j=0}^{n-1} exp (-k * τ) ^ j`, the closed form of the
[affine recurrence](post-dose-amount-succ.md) it satisfies.
