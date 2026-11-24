# Under equal mixed partials, the discharge solves the 1D wave equation

Let `a`, `g` and `A` be positive (wave speed, gravitational acceleration, pipe area), and let `h`,
`q` (head and discharge) and `h_t`, `h_x`, `q_t`, `q_x` be real functions of `(t, x)`. Suppose that
for all real `t` and `x`: `h(·, x)` and `q(·, x)` have the derivatives `h_t(t, x)` and `q_t(t, x)`
at `t`; `h(t, ·)` and `q(t, ·)` have the derivatives `h_x(t, x)` and `q_x(t, x)` at `x`; and the
water-hammer equations `h_t + (a² / (g A)) q_x = 0` and `q_t + g A h_x = 0` hold. Let moreover
`q_xx`, `h_xt` and `h_tx` be real functions of `(t, x)` such that, for all `t` and `x`, `q_x(t, ·)`
has the derivative `q_xx(t, x)` at `x`, `h_x(·, x)` has the derivative `h_xt(t, x)` at `t`, and
`h_t(t, ·)` has the derivative `h_tx(t, x)` at `x`. If `h_xt(t, x) = h_tx(t, x)` for all `t` and
`x`, then the discharge, read as the
[one-component field](../../waves-and-acoustics/travelling-wave-solutions-of-the-wave-equation/scalar-wave-field.md)
`u(t, x) = q(t, x₀)` on one-dimensional space (`x₀` the coordinate of the point `x`), satisfies the
wave equation with speed `a` at every time `t` and every point `x`:
`a² Δu(t, x) - ∂ₜ(∂ₜ u(·, x))(t) = 0`, where `Δ` is the vector Laplacian in space, here the second
derivative in `x₀`, and `∂ₜ(∂ₜ u(·, x))` is the iterated time derivative at the fixed point `x`.
