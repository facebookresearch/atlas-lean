# Fick's law with the continuity equation gives the diffusion equation

Let `D` be real and `c(x, t)` a concentration field. Suppose that at `(x, t)` the map `c(x, ·)` has
the derivative `c_t` at `t`, the map `x' ↦ ∂c/∂x(x', t)` has the derivative `c_xx` at `x`, and the
continuity equation `c_t + ∂J/∂x(x, t) = 0` holds for the [Fick flux](fick-flux.md) `J = -D ∂c/∂x`.
Then

`∂c/∂t(x, t) = D c_xx`.

Fick's law alone does not give this; the continuity equation is needed.
