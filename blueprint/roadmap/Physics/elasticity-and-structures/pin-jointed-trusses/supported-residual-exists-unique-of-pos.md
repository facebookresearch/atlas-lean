# Unique displacement and residual reaction for a full joint load

Let `J` (joints), `M` (members) and `F` (free coordinates) be finite sets, with joint positions
`r_j` in the plane, member `e` joining joint `a_e` to joint `b_e`, a matrix `S` from the free
coordinates to the joint displacement coordinates (two per joint), and member weights `k_e`. Let
`K = (B S)ᵀ diag(k) (B S)` be the supported stiffness, with the
[compatibility matrix](axial-compatibility.md) `B`. Suppose that `K` is positive definite. Then for
every load `g` on all joint coordinates there is exactly one pair of a displacement `u` on the free
coordinates and a residual `ρ` on all joint coordinates with `(Bᵀ diag(k) B) (S u) = g + ρ` and
`Sᵀ ρ = 0`. The residual is the vector `(Bᵀ diag(k) B) (S u) - g`; no expansion in a basis of
reactions is stated.
