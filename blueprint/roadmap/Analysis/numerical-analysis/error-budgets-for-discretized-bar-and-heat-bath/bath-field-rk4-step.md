# A Runge–Kutta step of the bath field multiplies the excess by R(z)

For all real `C`, `G`, `T_amb`, `t`, `T` and `dt`, one
[classical Runge–Kutta step](../runge-kutta-methods/rk4.md) of size `dt` of the
[bath field](bath-field.md) from `T` is `T_amb + (T - T_amb) R(z)`, with
`R(z) = 1 + z + z²/2 + z³/6 + z⁴/24` and `z = (-1/τ) dt`, `τ = C / G`. With the convention
`a / 0 = 0`, `-1/τ = 0` when `τ = 0`.
