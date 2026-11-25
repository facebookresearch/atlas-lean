# Finite sealed-end mode expansion

For real numbers `τ`, `ℓ` and `L`, a finite set `s` of natural numbers, real coefficients `a_n` and
real `t` and `x`, the finite sealed-end mode expansion is

`V(t, x) = ∑_{n ∈ s} a_n e^(-k_n t) cos (n π x / L)`,

where `k_n` is the [rate](decay-rate.md) of the `n`-th [mode](cos-mode.md). It is defined for all
real `t` and `x`, with the conventions of the rates and modes (for example every `k_n` is `0` when
`τ = 0`, and every mode is `1` when `L = 0`). For `τ ≠ 0` it
[solves the cable equation](is-cable-solution-cable-sum.md) at all times, and for `L ≠ 0` it has
[sealed ends](sealed-ends-cable-sum.md).
