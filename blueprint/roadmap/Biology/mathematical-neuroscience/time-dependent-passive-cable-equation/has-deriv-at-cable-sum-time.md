# Time derivative of the finite expansion

For all real `τ`, `ℓ`, `L`, `t` and `x`, every finite set `s` of natural numbers and all real
coefficients `a_n`, the [finite expansion](cable-sum.md)
`V(t, x) = ∑_{n ∈ s} a_n e^(-k_n t) cos (n π x / L)` is differentiable in time at `t`, term by
term:

`∂ₜV(t, x) = ∑_{n ∈ s} a_n (-k_n) e^(-k_n t) cos (n π x / L)`,

where `k_n` is the [rate](decay-rate.md) of the `n`-th mode.
