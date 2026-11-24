# Frame Stiffness

Six-DOF local frame-element stiffness matrix, in the fixed
ordering `(u1, v1, θ1, u2, v2, θ2)`: axial displacement,
transverse deflection, and rotation at end 1, then the same three
coordinates at end 2. It combines the axial block
`axialStiffness` on `(u1, u2)` with the bending block
`beamStiffness` on `(v1, θ1, v2, θ2)`, with no axial-bending
coupling. The definition is the totalized formula.
