# Unit-load identity in separation form

Let `J` (joints), `M` (members) and `F` (free coordinates) be finite sets, with joint positions
`r_j` in the plane, member `e` joining joint `a_e` to joint `b_e`, a matrix `S` from the free
coordinates to the joint displacement coordinates (two per joint), and member weights `k_e`. Let
`K = (B S)ᵀ diag(k) (B S)` be the supported stiffness, with the
[compatibility matrix](axial-compatibility.md) `B`. Suppose that `K` is positive definite. Let
`aout` be a fixed output functional on `F`, `η = K⁻¹ aout` its
[influence vector](influence-vector.md) and `f ↦ η · f` its
[unit-load response](unit-load-response.md). If `K u = f`, then `aout · u = n · (B S u)` with
`n = diag(k) (B S η)`, the separation-form member coefficients of the unit-load case (for a member
of positive length, axial force divided by member length); the entries of `B S u` are member length
times elongation.
