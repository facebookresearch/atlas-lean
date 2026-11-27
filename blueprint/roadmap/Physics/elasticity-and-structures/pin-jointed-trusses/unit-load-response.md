# Unit-load response of a supported truss

Let `J` (joints), `M` (members) and `F` (free coordinates) be finite sets, with joint positions
`r_j` in the plane, member `e` joining joint `a_e` to joint `b_e`, a matrix `S` from the free
coordinates to the joint displacement coordinates (two per joint), and member weights `k_e`. Let
`K = (B S)ᵀ diag(k) (B S)` be the supported stiffness, with the
[compatibility matrix](axial-compatibility.md) `B`. For an output functional `aout` on the free
coordinates, with [influence vector](influence-vector.md) `η = K⁻¹ aout`, the unit-load response is
the linear map `f ↦ η · f` on the loads `f` on the free coordinates. No positivity of the weights
and no definiteness of `K` is assumed: the inverse of a singular matrix is the zero matrix by
convention, so that `η = 0` and every response is `0` when `K` is singular. The physical reading is
a positive definite `K`.
