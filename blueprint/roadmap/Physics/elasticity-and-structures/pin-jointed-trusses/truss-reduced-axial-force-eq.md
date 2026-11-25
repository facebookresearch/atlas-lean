# Determinate truss axial forces from statics

Let `J` (joints) and `M` (members) be finite sets, with joint positions `r_j` in the plane and
member `e` joining joint `a_e` to joint `b_e`, and let `S` be a matrix from free coordinates indexed
by the members to the joint displacement coordinates, such that `B S` is invertible, with the
[compatibility matrix](axial-compatibility.md) `B`. Let `k` be member weights and `u` a solution of
`(B S)ᵀ diag(k) (B S) u = f`, and let `s = diag(k) (B S u)` be the separation-form member
coefficients (axial force divided by member length). Then the physical axial forces `s_e L_e`
(tension positive), `L_e` being the Euclidean length of member `e`, are `(((B S)ᵀ)⁻¹ f)_e L_e`: the
reduced statics solution rescaled member by member by the length.
