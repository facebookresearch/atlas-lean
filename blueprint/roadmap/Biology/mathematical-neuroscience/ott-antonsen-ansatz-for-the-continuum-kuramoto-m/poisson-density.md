# Poisson Density

The Poisson-kernel density of Eq. (8) (the density `f / g` on the ansatz manifold):
Mathlib's Poisson kernel of the unit disk at the point `ᾱ`, evaluated at `e^{iθ}`, divided by
`2π`. It equals `(1 - |α|²) / (2π |1 - α e^{iθ}|²)`, since `|e^{iθ} - ᾱ| = |1 - α e^{iθ}|`, and
`(1 - |α|²) / (2π ((1 - |α|)² + 4 |α| sin² ((θ - ψ)/2)))` for `α = |α| e^{-iψ}`.
