# Supported truss stiffness quadratic form as a member sum

Let `J` (joints), `M` (members) and `F` (free coordinates) be finite sets, with joint positions
`r_j` in the plane, member `e` joining joint `a_e` to joint `b_e`, a matrix `S` from the free
coordinates to the joint displacement coordinates (two per joint), and member weights `k_e`. Let
`K = (B S)ᵀ diag(k) (B S)` be the supported stiffness, with the
[compatibility matrix](axial-compatibility.md) `B`. For all real weights and every `u` on the free
coordinates, `u · K u = ∑_e k_e ((B S u)_e)²`: twice the linearized stored energy in the physical
reading, where the weights are positive.
