# Sensor readings are the observation matrix times the load parameters

Let `J` (joints), `M` (members) and `F` (free coordinates) be finite sets, with joint positions
`r_j` in the plane, member `e` joining joint `a_e` to joint `b_e`, a matrix `S` from the free
coordinates to the joint displacement coordinates (two per joint), and member weights `k_e`. Let
`K = (B S)ᵀ diag(k) (B S)` be the supported stiffness, with the
[compatibility matrix](axial-compatibility.md) `B`. Suppose that `K` is positive definite. Let `C`
be an `n_m × n_f` sensor matrix and `B_load` an `n_f × n_p` load matrix, the free coordinates being
`n_f` in number, and let `H = C K⁻¹ B_load` be the
[load observation matrix](load-observation-matrix.md). If `K u = B_load θ` for a load-parameter
vector `θ`, then `C u = H θ`.
