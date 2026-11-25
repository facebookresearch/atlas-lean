# Supported truss with axial weights and no null mode: unique response

Let `J`, `M` and `F` be finite sets, with joint positions `r_j` in the plane, member `e` joining
joint `a_e` to joint `b_e`, and a matrix `S` from the free coordinates to the joint displacement
coordinates, and let the [compatibility matrix](axial-compatibility.md) `B` be the separation-form
compatibility matrix. Let `E_e > 0` and `A_e > 0` for every member, and let the end positions of
every member be distinct, `r_{a_e} ≠ r_{b_e}`, so that its Euclidean length `L_e` is positive. Let
`K = (B S)ᵀ diag(E A / L³) (B S)` be the supported stiffness with the separation-form axial weights
`E_e A_e / L_e³`. Suppose that `B S u = 0` implies `u = 0`. Then every load `f` on the free
coordinates has exactly one displacement `u` with `K u = f`, and every load `g` on all joint
coordinates has exactly one pair of a displacement `u` and a residual `ρ` with
`(Bᵀ diag(E A / L³) B) (S u) = g + ρ` and `Sᵀ ρ = 0`.
