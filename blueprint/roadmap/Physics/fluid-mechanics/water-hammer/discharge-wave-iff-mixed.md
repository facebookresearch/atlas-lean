# Discharge wave equation at a point iff the mixed partials of h agree

Let `a`, `g` and `A` be positive (wave speed, gravitational acceleration, pipe area), and let `h`,
`q` (head and discharge) and `h_t`, `h_x`, `q_t`, `q_x` be real functions of `(t, x)`. Suppose that
for all real `t` and `x`: `h(·, x)` and `q(·, x)` have the derivatives `h_t(t, x)` and `q_t(t, x)`
at `t`; `h(t, ·)` and `q(t, ·)` have the derivatives `h_x(t, x)` and `q_x(t, x)` at `x`; and the
water-hammer equations `h_t + (a² / (g A)) q_x = 0` and `q_t + g A h_x = 0` hold. Let moreover
`q_xx`, `h_xt` and `h_tx` be real functions of `(t, x)` such that, for all `t` and `x`, `q_x(t, ·)`
has the derivative `q_xx(t, x)` at `x`, `h_x(·, x)` has the derivative `h_xt(t, x)` at `t`, and
`h_t(t, ·)` has the derivative `h_tx(t, x)` at `x`. Then, at a given point `(t, x)`, `q_t(·, x)` has
the derivative `a² q_xx(t, x)` at `t`, which is the discharge wave equation `q_tt = a² q_xx` there,
if and only if `h_xt(t, x) = h_tx(t, x)`: the two mixed second partials of the head agree at
`(t, x)`. The hypotheses relating `h_t`, `h_x`, `q_t`, `q_x` to `h` and `q` are not needed for this
equivalence; the two water-hammer equations and the second derivatives are.
