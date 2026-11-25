# Separation-form compatibility matrix of a planar truss

Let `J` (joints) and `M` (members) be sets, with joint positions `r_j` in the plane and member `e`
joining joint `a_e` to joint `b_e`. The separation-form compatibility matrix `B` has rows indexed by
the members and columns by the joint coordinates `(j, k)`, `k ∈ {0, 1}`; its entry in row `e` and
column `(j, k)` is `([b_e = j] - [a_e = j]) (r_{b_e} - r_{a_e})_k`, where `[P]` is `1` if `P` holds
and `0` otherwise. Row `e` thus carries the separation vector `r_{b_e} - r_{a_e}` at the end joint
and its negative at the start joint.
