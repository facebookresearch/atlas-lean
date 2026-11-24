# Runge–Kutta steps of size τ/10 multiply the excess by 72387/80000

For real numbers `C > 0`, `G > 0`, `T_amb` and `Δ`, and a real sequence `X` with `X_0 = T_amb + Δ`
and `X_{j+1}` the [classical Runge–Kutta step](../runge-kutta-methods/rk4.md) of size `τ / 10` of
the [bath field](bath-field.md) from `X_j` at the time `j τ / 10` (`τ = C / G`), every term is
`X_j = T_amb + Δ (72387/80000)^j`.
