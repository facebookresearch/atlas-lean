# The supported stiffness is the full stiffness restricted by S

Let `J` (joints), `M` (members) and `F` (free coordinates) be finite sets, with joint positions
`r_j` in the plane, member `e` joining joint `a_e` to joint `b_e`, a matrix `S` from the free
coordinates to the joint displacement coordinates (two per joint), and member weights `k_e`. Let
`K = (B S)ᵀ diag(k) (B S)` be the supported stiffness, with the
[compatibility matrix](axial-compatibility.md) `B`. For all real weights, `K = Sᵀ (Bᵀ diag(k) B) S`:
the supported stiffness is the full stiffness `Bᵀ diag(k) B` restricted by the support map.
