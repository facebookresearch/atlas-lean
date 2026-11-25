# The static and kinematic certificates are complementary

For all real `L` and `Mp` and each critical section `e`, let `σ = (-Mp, Mp, -Mp)` be the collapse
moments and `θ = B (2 / L)` the hinge rotations of the normalized mechanism, with the
[hinge-rotation matrix](hinge-rotation.md) `B = (-2 / L, 4 / L, -2 / L)ᵀ` (a 3 × 1 matrix: rows the
critical sections at the left end, mid-span and right end; column the central deflection). Then
`Mp * |θ_e| = σ_e * θ_e`: the plastic dissipation leaves no slack. For `L ≠ 0` the rotations are
`θ = (-4 / L ^ 2, 8 / L ^ 2, -4 / L ^ 2)`, so `σ_e = Mp * sign(θ_e)`, and for `Mp > 0` each moment
has the sign of its hinge rotation. At `L = 0` the rotations are `0` by the convention `x / 0 = 0`
and both sides vanish. The physical reading is `L > 0` and `Mp > 0`.
