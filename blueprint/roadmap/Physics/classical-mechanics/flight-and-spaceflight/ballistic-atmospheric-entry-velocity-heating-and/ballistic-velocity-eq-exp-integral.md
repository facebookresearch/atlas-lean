# The velocity profile as an exponential of the column mass

Let `H ≠ 0`, and let `ρ₀`, `β`, `γ`, `h_e`, `v_e` and `h` be real. The
[finite-entry ballistic velocity profile](ballistic-velocity.md) equals

`v(h) = v_e exp((∫ from h_e to h of ρ(s) ds) / (2 β sin γ))`,

with `ρ(s) = ρ₀ exp(−s / H)` the [exponential density](exponential-density.md): its exponent is the
integral of the density from `h_e` to `h` (for `ρ₀ ≥ 0` the oriented column mass) divided by
`2 β sin γ`. With the convention `x / 0 = 0`, both sides equal `v_e` when `β sin γ = 0`. For `β > 0`
and `sin γ > 0` this is the integrated form of the
[altitude form of the drag equation](has-deriv-at-ballistic-velocity.md),
`dv/dh = ρ(h) v / (2 β sin γ)`.
