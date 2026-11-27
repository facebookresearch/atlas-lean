# Unit-load identity in physical axial forces

Let `J` (joints), `M` (members) and `F` (free coordinates) be finite sets, with joint positions
`r_j` in the plane, member `e` joining joint `a_e` to joint `b_e`, a matrix `S` from the free
coordinates to the joint displacement coordinates (two per joint), and member weights `k_e`. Let
`K = (B S)ᵀ diag(k) (B S)` be the supported stiffness, with the
[compatibility matrix](axial-compatibility.md) `B`. Suppose that every weight is positive,
`k_e > 0`, that `K` is positive definite and that the end positions of every member are distinct, so
that its Euclidean length `L_e` is positive. Let `aout` be a fixed output functional on `F`,
`η = K⁻¹ aout` its [influence vector](influence-vector.md) and `f ↦ η · f` its
[unit-load response](unit-load-response.md). Let `N = diag(k) (B S u)` and `n = diag(k) (B S η)`. If
`K u = f`, then `aout · u = ∑_e (n_e L_e) (N_e L_e) / (k_e L_e²)`, where `N_e L_e` and `n_e L_e` are
the physical axial forces (tension positive). For the physical weights `k_e = E_e A_e / L_e³` the
denominator `k_e L_e²` is `E_e A_e / L_e`, and the sum is the classical unit-load sum
`∑_e (n_e L_e) (N_e L_e) L_e / (E_e A_e)` of the physical axial forces.
