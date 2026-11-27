# Unit-load identity with inverse member weights

Let `J` (joints), `M` (members) and `F` (free coordinates) be finite sets, with joint positions
`r_j` in the plane, member `e` joining joint `a_e` to joint `b_e`, a matrix `S` from the free
coordinates to the joint displacement coordinates (two per joint), and member weights `k_e`. Let
`K = (B S)ᵀ diag(k) (B S)` be the supported stiffness, with the
[compatibility matrix](axial-compatibility.md) `B`. Suppose that every weight is positive,
`k_e > 0`, and that `K` is positive definite. Let `aout` be a fixed output functional on `F`,
`η = K⁻¹ aout` its [influence vector](influence-vector.md) and `f ↦ η · f` its
[unit-load response](unit-load-response.md). If `K u = f`, then `aout · u = n · (diag(1 / k) N)`
with `N = diag(k) (B S u)` and `n = diag(k) (B S η)`, the separation-form member coefficients (for a
member of positive length, axial force divided by member length) of the two load cases. For the
physical weights `E A / L³` the factors `1 / k_e` are `L_e³ / (E_e A_e)`, not the member
flexibilities `L_e / (E_e A_e)`.
