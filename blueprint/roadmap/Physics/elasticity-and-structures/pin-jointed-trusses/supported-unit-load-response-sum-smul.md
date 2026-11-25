# Superposition of unit-load responses over a finite load table

Let `J` (joints), `M` (members) and `F` (free coordinates) be finite sets, with joint positions
`r_j` in the plane, member `e` joining joint `a_e` to joint `b_e`, a matrix `S` from the free
coordinates to the joint displacement coordinates (two per joint), and member weights `k_e`. Let
`K = (B S)ᵀ diag(k) (B S)` be the supported stiffness, with the
[compatibility matrix](axial-compatibility.md) `B`. Let `aout` be a fixed output functional on `F`,
`η = K⁻¹ aout` its [influence vector](influence-vector.md) and `f ↦ η · f` its
[unit-load response](unit-load-response.md). For every finite set `s` of load cases, loads `f_i` and
real coefficients `w_i`, the response to `∑_{i ∈ s} w_i f_i` is `∑_{i ∈ s} w_i (η · f_i)`. No
positivity of the weights and no definiteness of `K` is assumed: the inverse of a singular matrix is
the zero matrix by convention, so that `η = 0` and every response is `0` when `K` is singular. The
physical reading is a positive definite `K`.
