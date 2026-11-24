# Erfc Profile

The constant-surface-concentration profile on the half-line `x ≥ 0`:
`erfcProfile cs D x t = cs · erfc(x / √(4Dt))`, the concentration at depth `x` and time `t` when
the surface `x = 0` is held at `cs` and the medium is initially empty. It is meant for `D > 0`,
`t > 0` and `x ≥ 0`. For `D > 0` and `t ≤ 0` the square root is `0`, `x / 0 = 0` and the value is
`cs` at every `x` (Lean's division convention), not the initial concentration `0`; the initial
condition is the limit `erfcProfile_initial`.
