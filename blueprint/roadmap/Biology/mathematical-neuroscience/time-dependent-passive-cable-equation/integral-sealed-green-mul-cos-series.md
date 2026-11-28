# Superposing point-charge responses reproduces the expansion for t > 0

For real numbers `τ > 0`, `ℓ ≠ 0` and `L ≠ 0`, real coefficients `a_n` with `∑_n |a_n| < ∞`,
every time `t > 0` and every real `x`, let `f(y) = ∑_{n ≥ 0} a_n cos (n π y / L)`. Then, with `G`
the [Green's function of the sealed cable](sealed-green.md),

`∫₀ᴸ G(t, x; y) f(y) dy = ∑_{n ≥ 0} a_n e^(-k_n t) cos (n π x / L)`,

the [infinite expansion](cable-series.md) at time `t`, where `k_n` is the [rate](decay-rate.md) of
the `n`-th mode. For `L > 0` this superposes the responses to the charges `f(y) dy` placed at the
points `y ∈ [0, L]`; for `L < 0` the integral is oriented.
