# A null mode rules out a unique supported displacement

Let `J` (joints), `M` (members) and `F` (free coordinates) be finite sets, with joint positions
`r_j` in the plane, member `e` joining joint `a_e` to joint `b_e`, a matrix `S` from the free
coordinates to the joint displacement coordinates (two per joint), and member weights `k_e`. Let
`K = (B S)ᵀ diag(k) (B S)` be the supported stiffness, with the
[compatibility matrix](axial-compatibility.md) `B`. For arbitrary real weights, if some `z ≠ 0` on
the free coordinates satisfies `B S z = 0` (no member stretches), then no load `f` has a unique
displacement `u` with `K u = f`. In particular an unsupported rigid motion or a supported mechanism
rules out a unique response.
