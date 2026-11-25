# The hinge rotations are the slope jumps of the mechanism

For all real `L` and `δ`, there are slopes `s₁` and `s₂` such that the
[mechanism deflection](mechanism-deflection.md) `2 * δ / L * min x (L - x)` has derivative `s₁` at
every `x` in `(0, L / 2)` and `s₂` at every `x` in `(L / 2, L)`, and the hinge rotations are the
slope jumps: `B δ = (0 - s₁, s₁ - s₂, s₂ - 0)` with the [hinge-rotation matrix](hinge-rotation.md)
`B = (-2 / L, 4 / L, -2 / L)ᵀ` (a 3 × 1 matrix: rows the critical sections at the left end, mid-span
and right end; column the central deflection). With zero slope at the clamped supports, each sagging
hinge rotation is the slope on its left minus the slope on its right. For `L > 0` the slopes are
`2 * δ / L` and `-(2 * δ / L)`; for `L ≤ 0` the two intervals are empty and the derivative
conditions are vacuous.
