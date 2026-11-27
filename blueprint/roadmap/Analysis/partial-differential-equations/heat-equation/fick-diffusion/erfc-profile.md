# Constant-surface-concentration diffusion profile

The profile `cs · erfc(x / √(4Dt))` on the half-line `x ≥ 0`: the
concentration at depth `x` and time `t` when the surface `x = 0` is held at
`cs` and the medium is initially empty. It is intended for `D > 0`, `t > 0`
and `x ≥ 0`. For `D > 0` and `t ≤ 0` the square root and the quotient are
taken to be `0`, so the value is `cs` at every `x`; the initial condition
holds only as the limit `t → 0⁺`.
