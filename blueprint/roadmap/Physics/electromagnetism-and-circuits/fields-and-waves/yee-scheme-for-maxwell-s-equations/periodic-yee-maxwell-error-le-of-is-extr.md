# Yee error bound for the fields of an extremal potential

Consider free space with permittivity `ε₀ > 0` and permeability `μ₀ > 0`, with the free-space speed
of light `c = 1 / √(ε₀ μ₀)`. On a periodic grid of `N > 0` cells of width `h > 0` with `L = N h`,
and a time step `dt > 0`, assume the Courant bound `c dt / h ≤ ρ < 1`. Let `A` be an infinitely
differentiable electromagnetic potential that is an extremum of the free-space Lagrangian with zero
current, and `E_y, H_z : ℝ² → ℝ` (functions of `(t, x)`) such that the electric and magnetic fields
of `A` are the [polarized fields](polarized-electric-field.md) `(0, E_y, 0)` and
[`(0, 0, μ₀ H_z)`](polarized-magnetic-field.md) (components at every time and point). Suppose `E_y`
and `H_z` are spatially periodic with period `L`, each three times continuously differentiable in
`t` for every fixed `x` and in `x` for every fixed `t`, with the
[third-derivative bounds](has-field-third-derivative-bounds.md) `MEt`, `MHt`, `MEx`, `MHx`. This is
the [error bound](periodic-yee-maxwell-error-le.md) with the Maxwell hypothesis replaced by the
extremum condition. Then for all initial grid fields `E0, H0 ∈ ℝᴺ` and every step `n` with
`n dt ≤ T`, the [normalized error](normalized-field-error.md) is at most
`√((1 + ρ) / (1 − ρ)) · (δ₀ + T √L (Mt dt² + c Mx h²) / 6)`, where `Mt = max(√ε₀ MEt, √μ₀ MHt)` and
`Mx = max(√ε₀ MEx, √μ₀ MHx)` are the [time](energy-time-bound.md) and [space](energy-space-bound.md)
bounds in energy coordinates, and `δ₀` is the
[normalized initial mismatch](normalized-initial-mismatch.md).
