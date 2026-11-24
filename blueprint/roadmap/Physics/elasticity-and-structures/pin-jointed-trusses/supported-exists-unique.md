# Positive weights and no null mode give a unique displacement

Let `J` (joints), `M` (members) and `F` (free coordinates) be finite sets, with joint positions
`r_j` in the plane, member `e` joining joint `a_e` to joint `b_e`, a matrix `S` from the free
coordinates to the joint displacement coordinates (two per joint), and member weights `k_e`. Let
`K = (B S)ᵀ diag(k) (B S)` be the supported stiffness, with the
[compatibility matrix](axial-compatibility.md) `B`. If every weight is positive, `k_e > 0`, and
`B S u = 0` implies `u = 0` (no supported null mode), then every load `f` on the free coordinates
has exactly one displacement `u` with `K u = f`.
