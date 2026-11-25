# Load observation matrix of a supported truss

Let `J` (joints), `M` (members) and `F` (free coordinates) be finite sets, with joint positions
`r_j` in the plane, member `e` joining joint `a_e` to joint `b_e`, a matrix `S` from the free
coordinates to the joint displacement coordinates (two per joint), and member weights `k_e`. Let
`K = (B S)ᵀ diag(k) (B S)` be the supported stiffness, with the
[compatibility matrix](axial-compatibility.md) `B`. For an `n_m × n_f` sensor matrix `C` and an
`n_f × n_p` load matrix `B_load`, the free coordinates being `n_f` in number, the load observation
matrix is `H = C K⁻¹ B_load`. The inverse of a singular matrix is the zero matrix by convention, so
that `H = 0` when `K` is singular; the physical reading is a positive definite `K`.
