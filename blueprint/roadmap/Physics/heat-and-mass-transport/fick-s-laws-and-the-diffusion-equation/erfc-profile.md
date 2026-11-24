# Error-function profile with surface concentration cs

For real `cs`, `D`, `x` and `t`, the error-function profile is

`C(x, t) = cs · erfc(x/√(4Dt))`,

with the [complementary error function](erfc.md): the concentration at depth `x` and time `t` when
the surface `x = 0` is held at `cs` and the half-line `x > 0` is initially empty. It is meant for
`D > 0`, `t > 0` and `x ≥ 0`. When `Dt ≤ 0`, for example for `D > 0` and `t ≤ 0`, the square root is
`0`, `x/0 = 0` and the value is `cs` at every `x`, not the initial concentration `0`; the initial
condition holds as the [limit as t → 0⁺](erfc-profile-initial.md).
