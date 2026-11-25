# Row action of the compatibility matrix

Let `J` be a finite set of joints, with positions `r_j` in the plane, and member `e` joining joint
`a_e` to joint `b_e`. For every joint displacement vector `u` and member `e`, the
[compatibility matrix](axial-compatibility.md) `B` satisfies
`(B u)_e = ∑_k (r_{b_e} - r_{a_e})_k (u(b_e, k) - u(a_e, k))`: the separation vector paired with the
relative displacement of the two end joints, that is the member length times the linearized
elongation in the physical reading.
