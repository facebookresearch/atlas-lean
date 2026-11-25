# The unit-load response equals the output of the displacement

Let `J` (joints), `M` (members) and `F` (free coordinates) be finite sets, with joint positions
`r_j` in the plane, member `e` joining joint `a_e` to joint `b_e`, a matrix `S` from the free
coordinates to the joint displacement coordinates (two per joint), and member weights `k_e`. Let
`K = (B S)ᵀ diag(k) (B S)` be the supported stiffness, with the
[compatibility matrix](axial-compatibility.md) `B`. Suppose that `K` is positive definite. Let
`aout` be a fixed output functional on `F`, `η = K⁻¹ aout` its
[influence vector](influence-vector.md) and `f ↦ η · f` its
[unit-load response](unit-load-response.md). If `K u = f`, then `η · f = aout · u`: the unit-load
response to `f` is the output of the displacement.
