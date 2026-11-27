# The inverse weights recover member length times elongation

Let `J` (joints), `M` (members) and `F` (free coordinates) be finite sets, with joint positions
`r_j` in the plane, member `e` joining joint `a_e` to joint `b_e`, a matrix `S` from the free
coordinates to the joint displacement coordinates (two per joint), and member weights `k_e`. Let
`K = (B S)ᵀ diag(k) (B S)` be the supported stiffness, with the
[compatibility matrix](axial-compatibility.md) `B`. If every weight is positive, `k_e > 0`, then for
every `u` on the free coordinates `diag(1 / k) (diag(k) (B S u)) = B S u`: the inverse weights map
the elastic coefficient vector back to the member pairings `(B S u)_e`, the member length times the
elongation.
