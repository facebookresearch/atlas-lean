# Runge–Kutta steps of size 3τ multiply the excess by 11/8

For real numbers `C > 0`, `G > 0`, `T_amb` and `Δ`, and a real sequence `X` with `X_0 = T_amb + Δ`
and `X_{j+1}` the [classical Runge–Kutta step](../runge-kutta-methods/rk4.md) of size `3 τ` of the
[bath field](bath-field.md) from `X_j` at the time `3 j τ`: the exact
[trajectory](bath-trajectory.md) satisfies `|T(t) - T_amb| ≤ |Δ|` for every `t ≥ 0`, while
`X_j = T_amb + Δ (11/8)^j` and `|X_j - T_amb| = (11/8)^j |Δ|` for every `j`.
