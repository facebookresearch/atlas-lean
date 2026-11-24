# Periodic C³ polarized vacuum fields give a smooth periodic solution

For free space with permittivity `ε₀ > 0` and permeability `μ₀ > 0` and the free-space speed of
light `c = 1 / √(ε₀ μ₀)`, and a real `L`: let `E_y, H_z : ℝ² → ℝ` (functions of `(t, x)`) be such
that the [polarized fields](polarized-electric-field.md) `(0, E_y, 0)` and
[`(0, 0, μ₀ H_z)`](polarized-magnetic-field.md) satisfy the
[source-free vacuum Maxwell equations in component form](../separable-vacuum-maxwell-fields/source-free-vacuum-maxwell.md)
at `c`; both are spatially periodic with period `L` (`E_y(t, x + L) = E_y(t, x)` and
`H_z(t, x + L) = H_z(t, x)` for all `t`, `x`); each is three times continuously differentiable in
`t` for every fixed `x` and in `x` for every fixed `t`; and they have the
[third-derivative bounds](has-field-third-derivative-bounds.md) `MEt`, `MHt`, `MEx`, `MHx`. Then the
energy coordinates [`u = √ε₀ E_y`](energy-u.md) and [`v = −√μ₀ H_z`](energy-v.md) solve
`u_t = c v_x`, `v_t = c u_x`, are spatially periodic with period `L`, are three times continuously
differentiable in each argument separately, and their third time and space derivatives are bounded
in absolute value by `Mt = max(√ε₀ MEt, √μ₀ MHt)` and `Mx = max(√ε₀ MEx, √μ₀ MHx)`.
