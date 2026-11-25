# Local stiffness matrix of a planar frame element

For an axial rigidity `EA`, a flexural rigidity `EI` and a length `L` (real numbers), the local
stiffness matrix of a planar frame element in the coordinates `(u1, v1, θ1, u2, v2, θ2)` (axial
displacement, transverse deflection and rotation at end 1, then at end 2) has the
[axial stiffness](axial-stiffness.md) `(EA / L) [[1, -1], [-1, 1]]` on `(u1, u2)` and the bending
entries of the [beam stiffness matrix](beam-stiffness.md) on `(v1, θ1, v2, θ2)` (`12 EI / L ^ 3`,
`6 EI / L ^ 2`, `4 EI / L`, `2 EI / L` with their signs), and no axial–bending coupling. It is
defined for all real inputs; at `L = 0` it is the zero matrix, by the convention `x / 0 = 0`. The
physical reading is `EA > 0`, `EI > 0` and `L > 0`.
