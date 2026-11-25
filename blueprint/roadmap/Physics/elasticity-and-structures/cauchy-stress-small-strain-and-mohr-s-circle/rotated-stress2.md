# Plane stress in axes rotated by θ

For a real `2 × 2` matrix `σ₂` and `θ ∈ ℝ`, the stress in the axes rotated by `θ` is
`σ₂' = Q(θ) σ₂ Q(θ)ᵀ`, where `Q(θ)` is the [axis-rotation matrix](rotation-matrix2.md) with rows
`e₀' = (cos θ, sin θ)` and `e₁' = (-sin θ, cos θ)`, the unit vectors of the new axes. Its entry
`(i, j)` is `e_i' · σ₂ e_j'`. The definition takes any `2 × 2` matrix; the transformation formulas
for the [normal stress σx'](rotated-stress2-00.md), the [normal stress σy'](rotated-stress2-11.md)
and the [shear stress τx'y'](rotated-stress2-01.md) are stated for a symmetric `σ₂`.
