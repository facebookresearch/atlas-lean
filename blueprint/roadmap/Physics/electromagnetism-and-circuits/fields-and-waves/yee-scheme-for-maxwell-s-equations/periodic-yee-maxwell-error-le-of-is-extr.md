# Yee error bound for the fields of an extremal potential

Under the grid, Courant, periodicity, smoothness and third-derivative hypotheses of the
[error bound](periodic-yee-maxwell-error-le.md), replace the Maxwell hypothesis by: an infinitely
differentiable electromagnetic potential `A` that is an extremum of the free-space Lagrangian with
zero current, whose electric and magnetic fields are the
[polarized fields](polarized-electric-field.md) `(0, E_y, 0)` and
[`(0, 0, μ₀ H_z)`](polarized-magnetic-field.md) (components at every time and point). Then for all
initial grid fields `E0, H0 ∈ ℝᴺ` and every step `n` with `n dt ≤ T`, the
[normalized error](normalized-field-error.md) is at most
`√((1 + ρ) / (1 − ρ)) · (E₀ + T √L (Mt dt² + c Mx h²) / 6)`, where `Mt = max(√ε₀ MEt, √μ₀ MHt)` and
`Mx = max(√ε₀ MEx, √μ₀ MHx)` are the [time](energy-time-bound.md) and [space](energy-space-bound.md)
bounds in energy coordinates, and `E₀` is the
[normalized initial mismatch](normalized-initial-mismatch.md).
