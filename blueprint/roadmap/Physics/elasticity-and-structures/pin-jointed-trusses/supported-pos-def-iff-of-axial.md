# Rigidity of a supported truss with axial weights EA over L cubed

Let `J`, `M` and `F` be finite sets, with joint positions `r_j` in the plane, member `e` joining
joint `a_e` to joint `b_e`, and a matrix `S` from the free coordinates to the joint displacement
coordinates, and let the [compatibility matrix](axial-compatibility.md) `B` be the separation-form
compatibility matrix. Let `E_e > 0` and `A_e > 0` for every member, and let the end positions of
every member be distinct, `r_{a_e} ≠ r_{b_e}`, so that its Euclidean length `L_e` is positive. Let
`K = (B S)ᵀ diag(E A / L³) (B S)` be the supported stiffness with the separation-form axial weights
`E_e A_e / L_e³`. Then `K` is positive definite if and only if `B S u = 0` implies `u = 0`. The
kernel condition is on the free coordinates `u`; it reads as the absence of supported joint
mechanisms when `S` is injective.
