# Inertial components of a planar state of the orbit-plane frame

For an orientation `Q ∈ SO(3)` of the orbit-plane frame (a rotation matrix, `Qᵀ Q = I` and
`det Q = 1`), a planar position or velocity `z : ℝ → ℂ` of time and a time `t`, the spatial state is
`Q (Re z(t), Im z(t), 0) ∈ ℝ³`, the inertial components given by the
[passive component map](../../rigid-bodies-and-mechanisms/body-fixed-and-inertial-frames/body-to-inertial-vec.md)
`v_I = Q v_B` from the [body components](planar-to-body.md) of `z(t)`. With `e₁, e₂, e₃` the
standard basis, the columns `Q e₁` and `Q e₂` span the orbit plane and `Q e₃ = Q e₁ × Q e₂` is its
oriented normal.
