# Reciprocal work for two loads on one supported truss

Let `J` (joints), `M` (members) and `F` (free coordinates) be finite sets, with joint positions
`r_j` in the plane, member `e` joining joint `a_e` to joint `b_e`, a matrix `S` from the free
coordinates to the joint displacement coordinates (two per joint), and member weights `k_e`. Let
`K = (B S)ᵀ diag(k) (B S)` be the supported stiffness, with the
[compatibility matrix](axial-compatibility.md) `B`. For all real weights, if `K u = f` and
`K v = g`, then `f · v = g · u`: the work of `f` through `v` equals the work of `g` through `u`. The
two load cases share the stiffness, the supports and the reference geometry.
