# A convex combination over one load case is that load case

Let `J` (joints), `M` (members) and `F` (free coordinates) be finite sets, with joint positions
`r_j` in the plane, member `e` joining joint `a_e` to joint `b_e`, a matrix `S` from the free
coordinates to the joint displacement coordinates (two per joint), and member weights `k_e`. Let
`K = (B S)ᵀ diag(k) (B S)` be the supported stiffness, with the
[compatibility matrix](axial-compatibility.md) `B`. Let `aout` be a fixed output functional on `F`,
`η = K⁻¹ aout` its [influence vector](influence-vector.md) and `f ↦ η · f` its
[unit-load response](unit-load-response.md). For a load case `i` with load `f_i` and coefficient
`w_i = 1`, the response to `w_i f_i` is the response to `f_i`. No positivity of the weights and no
definiteness of `K` is assumed: the inverse of a singular matrix is the zero matrix by convention,
so that `η = 0` and every response is `0` when `K` is singular. The physical reading is a positive
definite `K`.
