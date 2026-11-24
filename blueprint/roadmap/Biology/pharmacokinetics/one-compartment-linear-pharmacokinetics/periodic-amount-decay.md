# Decay between events

For `t` in the window
`[n * tau, (n + 1) * tau)` of the fixed-spacing schedule (so
`⌊t / tau⌋₊ = n`), the amount
`A t = ∑ i ∈ range (⌊t / tau⌋₊ + 1), D * exp (-k * (t - i * tau))`
is the amount just after the `n`-th dose decayed freely over
`t - n * tau`. The dose at `t = n * tau` itself is included (the
`i = n` term is `D * exp 0 = D` at the event instant).
