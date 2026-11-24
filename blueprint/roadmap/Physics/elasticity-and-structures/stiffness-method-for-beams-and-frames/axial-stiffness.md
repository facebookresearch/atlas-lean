# Stiffness matrix of a two-node axial element

For an axial rigidity `EA` and a length `L` (real numbers), the stiffness matrix of a two-node axial
element in the coordinates `(u1, u2)` is `(EA / L) [[1, -1], [-1, 1]]`. It is defined for all real
`EA` and `L`; at `L = 0` it is the zero matrix, by the convention `x / 0 = 0`. The physical reading
is `EA > 0` and `L > 0`.
