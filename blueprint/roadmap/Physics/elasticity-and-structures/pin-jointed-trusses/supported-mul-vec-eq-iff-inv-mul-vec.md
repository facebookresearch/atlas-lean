# Explicit supported displacement by the inverse stiffness

Let `J` (joints), `M` (members) and `F` (free coordinates) be finite sets, with joint positions
`r_j` in the plane, member `e` joining joint `a_e` to joint `b_e`, a matrix `S` from the free
coordinates to the joint displacement coordinates (two per joint), and member weights `k_e`. Let
`K = (B S)ᵀ diag(k) (B S)` be the supported stiffness, with the
[compatibility matrix](axial-compatibility.md) `B`. Suppose that `K` is positive definite. Then for
all `u` and `f` on the free coordinates, `K u = f` if and only if `u = K⁻¹ f`.
