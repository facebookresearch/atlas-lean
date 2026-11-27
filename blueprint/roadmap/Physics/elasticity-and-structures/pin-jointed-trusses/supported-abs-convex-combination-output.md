# Absolute hull bound for the output of convex load combinations

Let `J` (joints), `M` (members) and `F` (free coordinates) be finite sets, with joint positions
`r_j` in the plane, member `e` joining joint `a_e` to joint `b_e`, a matrix `S` from the free
coordinates to the joint displacement coordinates (two per joint), and member weights `k_e`. Let
`K = (B S)ᵀ diag(k) (B S)` be the supported stiffness, with the
[compatibility matrix](axial-compatibility.md) `B`. Suppose that `K` is positive definite. Let
`aout` be an output functional on the free coordinates. Let `s` be a nonempty finite set of load
cases with loads `f_i` and coefficients `w_i ≥ 0` (`i ∈ s`) summing to `1`. If `K u_i = f_i` for
every `i ∈ s` and `K u₀ = ∑_i w_i f_i`, then `|aout · u₀| ≤ max_i |aout · u_i|`.
