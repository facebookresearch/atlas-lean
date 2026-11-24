# Unit-direction compatibility matrix of a planar truss

With the members, joints and positions of the
[separation-form compatibility matrix](axial-compatibility.md) `B`, the unit-direction compatibility
matrix `B_u` has the entries `B_u(e, (j, k)) = B(e, (j, k)) / L_e`, `L_e` being the Euclidean length
of member `e`. A zero-length member gives a zero row, by the convention `0⁻¹ = 0`.
