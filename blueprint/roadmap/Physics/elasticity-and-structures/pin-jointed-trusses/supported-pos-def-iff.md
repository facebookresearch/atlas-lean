# Positive definiteness of the supported truss stiffness

Let `J` (joints), `M` (members) and `F` (free coordinates) be finite sets, with joint positions
`r_j` in the plane, member `e` joining joint `a_e` to joint `b_e`, a matrix `S` from the free
coordinates to the joint displacement coordinates (two per joint), and member weights `k_e`. Let
`K = (B S)ᵀ diag(k) (B S)` be the supported stiffness, with the
[compatibility matrix](axial-compatibility.md) `B`. If every weight is positive, `k_e > 0`, then `K`
is positive definite if and only if `B S` has trivial kernel: `B S u = 0` implies `u = 0`, that is,
the kernel of the linear map `u ↦ B S u` is `{0}`. For an
arbitrary `S` a kernel vector `u` need not give a nonzero joint displacement `S u`; reading the
kernel as supported mechanisms needs `S` injective, as for a selection of coordinates. Connectivity
of the members is not assumed and does not suffice.
