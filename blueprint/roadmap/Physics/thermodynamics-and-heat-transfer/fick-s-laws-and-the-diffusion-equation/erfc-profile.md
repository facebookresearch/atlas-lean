# Error-function profile with surface concentration cs

For real `cs`, `D`, `x` and `t`, the error-function profile is

`C(x, t) = cs · erfc(x/√(4Dt))`,

with the [complementary error function](erfc.md). It is meant for `D > 0`, `t > 0` and `x ≥ 0`, as
the concentration at depth `x` and time `t` when the surface `x = 0` is held at `cs` and the
half-line `x > 0` is initially empty: for `D > 0` and `t > 0` it
[solves the diffusion equation](erfc-profile-pde.md) `∂C/∂t = D ∂²C/∂x²` and
[equals `cs` at the surface](erfc-profile-surface.md), and for `x > 0` and `D > 0` it
[tends to `0` as `t → 0⁺`](erfc-profile-initial.md). When `Dt ≤ 0`, for example for `D > 0` and
`t ≤ 0`, the square root is `0`, `x/0 = 0` and the value is `cs` at every `x`, not the initial
concentration `0`.
