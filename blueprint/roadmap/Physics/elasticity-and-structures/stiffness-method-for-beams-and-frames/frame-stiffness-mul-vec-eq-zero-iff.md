# The kernel of the frame stiffness matrix is the planar rigid motions

For `EA > 0`, `EI > 0` and `L > 0` and every `d ∈ ℝ⁶`, the
[frame stiffness matrix](frame-stiffness.md) `K_f` satisfies `K_f d = 0` if and only if
`d = a (1, 0, 0, 1, 0, 0) + b (0, 1, 0, 0, 1, 0) + c (0, 0, 1, 0, L, 1)` for some real `a`, `b` and
`c`: the kernel is spanned by the axial translation, the transverse translation and the rigid
rotation, in the order `(u1, v1, θ1, u2, v2, θ2)`.
