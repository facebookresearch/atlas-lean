# Charging transient of a cable sealed at x = L

For real numbers `τ`, `ℓ`, `L` and `c`, a finite set `s` of natural numbers, real coefficients
`a_n` and real `t` and `x`, the charging transient is

`V(t, x) = c cosh ((L - x) / ℓ) + ∑_{n ∈ s} a_n e^(-k_n t) cos (n π x / L)`:

a multiple of the [steady profile](sealed-steady.md) sealed at `x = L` plus a
[finite expansion](cable-sum.md), with `k_n` the [rate](decay-rate.md) of the `n`-th mode. For
`τ ≠ 0` and `ℓ ≠ 0` it [solves the cable equation](is-cable-solution-charging-sum.md); for
`L ≠ 0` it is sealed at `x = L` and has the constant slope `-c sinh (L / ℓ) / ℓ` at `x = 0`, the
response to a constant injected current ([boundary slopes](deriv-charging-sum-ends.md)); for
`τ > 0` it tends to the steady profile `c cosh ((L - x) / ℓ)` ([limit](tendsto-charging-sum.md)).
