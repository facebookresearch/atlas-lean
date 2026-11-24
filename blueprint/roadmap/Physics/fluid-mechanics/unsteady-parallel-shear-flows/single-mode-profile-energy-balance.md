# Energy balance of the single-mode shear flow

Let `ρ > 0` and `L > 0`, let `A`, `μ` and `t` be real, `ν = μ / ρ` and `s = exp(-ν (π / L)² t)`, and
let `U` be the [single-mode profile](single-mode-profile.md)
`U(t, y) = A y / L - (A / π) sin(π y / L) exp(-ν (π / L)² t)`. Then the dissipation is
`μ ∫_0^L U_y(t, y)² dy = μ A² (1 + s² / 2) / L`, the work of the moving wall is
`μ U_y(t, L) A = μ A² (1 + s) / L`, and the
[kinetic energy per unit wall area](shear-kinetic-energy.md) `K(t) = ∫_0^L ρ U(t, y)² / 2 dy` has
the derivative `K'(t) = μ A² s (2 - s) / (2 L)`.
