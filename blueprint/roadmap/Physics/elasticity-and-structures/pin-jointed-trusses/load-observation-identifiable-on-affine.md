# With trivial sensor and load kernels, load parameters are identifiable

Let `J` (joints), `M` (members) and `F` (free coordinates) be finite sets, with joint positions
`r_j` in the plane, member `e` joining joint `a_e` to joint `b_e`, a matrix `S` from the free
coordinates to the joint displacement coordinates (two per joint), and member weights `k_e`. Let
`K = (B S)ᵀ diag(k) (B S)` be the supported stiffness, with the
[compatibility matrix](axial-compatibility.md) `B`. Suppose that `K` is positive definite. Let `C`
be an `n_m × n_f` sensor matrix and `B_load` an `n_f × n_p` load matrix (its columns need not be
independent), the free coordinates being `n_f` in number, and let `H = C K⁻¹ B_load` be the
[load observation matrix](load-observation-matrix.md). Let `θ₀` be a load-parameter vector and `V` a
linear subspace of `ℝ^{n_p}`. If `C w = 0` implies `w = 0`, and `B_load v = 0` with `v ∈ V` implies
`v = 0`, then `H` is injective on the affine subspace `θ₀ + V`: the load parameters there are
identifiable from the readings. The two kernel conditions are sufficient, not necessary: the exact
obstruction is a nonzero direction of `V` in the kernel of `H`.
