# Decay between events

For a dosing interval `τ > 0`, real `D` and `k`, a time `t ≥ 0` and a natural number `n` with
`⌊t / τ⌋₊ = n`, that is `t` in the window `[n * τ, (n + 1) * τ)`, the amount
`A(t) = ∑_{i=0}^{⌊t / τ⌋₊} D * exp (-k * (t - i * τ))` of the fixed-spacing schedule is the
[amount just after dose](post-dose-amount.md) `n`,
`P(n) = ∑_{i=0}^{n} D * exp (-k * (n * τ - i * τ))`, decayed freely over `t - n * τ`:
`A(t) = exp (-k * (t - n * τ)) * P(n)`. The dose at `t = n * τ` itself is included: the `i = n` term
is `D * exp 0 = D` at the event instant.
