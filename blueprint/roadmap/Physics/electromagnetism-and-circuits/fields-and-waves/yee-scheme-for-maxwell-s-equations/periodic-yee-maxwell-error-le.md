# Error bound of the periodic Yee scheme for a polarized vacuum field

Consider free space with permittivity `ε₀ > 0` and permeability `μ₀ > 0`, with the free-space speed
of light `c = 1 / √(ε₀ μ₀)`. On a periodic grid of `N > 0` cells of width `h > 0` with `L = N h`,
and a time step `dt > 0`, assume the Courant bound `c dt / h ≤ ρ < 1`. Let `E_y, H_z : ℝ² → ℝ`
(functions of `(t, x)`) be such that the [polarized fields](polarized-electric-field.md)
`(0, E_y, 0)` and [`(0, 0, μ₀ H_z)`](polarized-magnetic-field.md) satisfy the
[source-free vacuum Maxwell equations in component form](../separable-vacuum-maxwell-fields/source-free-vacuum-maxwell.md)
at `c`; both are spatially periodic with period `L` (`E_y(t, x + L) = E_y(t, x)` and
`H_z(t, x + L) = H_z(t, x)` for all `t`, `x`); each is three times continuously differentiable in
`t` for every fixed `x` and in `x` for every fixed `t`; and they have the
[third-derivative bounds](has-field-third-derivative-bounds.md) `MEt`, `MHt`, `MEx`, `MHx`. Then for
all initial grid fields `E0, H0 ∈ ℝᴺ` and every step `n` with `n dt ≤ T`, the
[normalized error](normalized-field-error.md) of the `n`-th
[physical Yee iterate](physical-yee-iterate.md) is at most
`√((1 + ρ) / (1 − ρ)) · (δ₀ + T √L (Mt dt² + c Mx h²) / 6)`, where `Mt = max(√ε₀ MEt, √μ₀ MHt)` and
`Mx = max(√ε₀ MEx, √μ₀ MHx)` are the [time](energy-time-bound.md) and [space](energy-space-bound.md)
bounds in energy coordinates, and `δ₀` is the
[normalized initial mismatch](normalized-initial-mismatch.md).
