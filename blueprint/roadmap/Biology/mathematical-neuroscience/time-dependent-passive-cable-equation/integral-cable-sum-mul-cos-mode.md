# For L ≠ 0, cosine coefficients of the finite expansion

For real `L ≠ 0`, all real `τ`, `ℓ` and `t`, every finite set `s` of natural numbers, all real
coefficients `a_m` and every natural number `n`, the [finite expansion](cable-sum.md) satisfies

`∫₀ᴸ V(t, x) cos (n π x / L) dx = a_n e^(-k_n t) c_n` if `n ∈ s`, and `0` otherwise,

where `k_n` is the [rate](decay-rate.md) of the `n`-th mode and `c_n` is its self-inner-product
`∫₀ᴸ cos (n π x / L)² dx`: `c_0 = L` and `c_n = L / 2` for `n ≥ 1`
([orthogonality](integral-cos-mode-mul-cos-mode.md)). The integral is oriented: for `L < 0` it is
minus the integral over `[L, 0]`.
