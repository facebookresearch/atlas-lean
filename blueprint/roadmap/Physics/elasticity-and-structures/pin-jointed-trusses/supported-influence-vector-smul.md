# Scaling the output scales the influence vector

Let `J` (joints), `M` (members) and `F` (free coordinates) be finite sets, with joint positions
`r_j` in the plane, member `e` joining joint `a_e` to joint `b_e`, a matrix `S` from the free
coordinates to the joint displacement coordinates (two per joint), and member weights `k_e`. Let
`K = (B S)ᵀ diag(k) (B S)` be the supported stiffness, with the
[compatibility matrix](axial-compatibility.md) `B`. For every real `c` and every output functional
`aout`, the [influence vector](influence-vector.md) of `c aout` is `c` times that of `aout`:
`K⁻¹ (c aout) = c K⁻¹ aout`. No definiteness of `K` is assumed; the inverse of a singular matrix is
the zero matrix by convention.
