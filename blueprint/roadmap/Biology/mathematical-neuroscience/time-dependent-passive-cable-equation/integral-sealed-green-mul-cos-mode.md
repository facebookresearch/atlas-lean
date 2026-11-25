# Cosine coefficients of the sealed-cable Green's function for t > 0

For real numbers `τ > 0`, `ℓ ≠ 0` and `L ≠ 0`, every real source position `x₀`,
every time `t > 0` and every natural number `n`, the [Green's function of the sealed cable](sealed-green.md)
satisfies

`∫₀ᴸ G(t, x; x₀) cos (n π x / L) dx = e^(-k_n t) cos (n π x₀ / L)`,

where `k_n` is the [rate](decay-rate.md) of the `n`-th mode: the value of the `n`-th mode at the
source, decayed at the mode's rate. The integral is oriented: for `L < 0` it is minus the integral
over `[L, 0]`.
