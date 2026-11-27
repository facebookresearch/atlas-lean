# At a dose time the trajectory equals the post-dose amount

For a dosing interval `τ > 0`, real `D` and `k` and every natural number `n`, the periodic
trajectory `A(t) = ∑_{i=0}^{⌊t / τ⌋₊} D * exp (-k * (t - i * τ))` at the event time `t = n * τ` is
the [amount just after dose](post-dose-amount.md) `n`,
`P(n) = ∑_{i=0}^{n} D * exp (-k * (n * τ - i * τ))`, since `⌊n * τ / τ⌋₊ = n`.
