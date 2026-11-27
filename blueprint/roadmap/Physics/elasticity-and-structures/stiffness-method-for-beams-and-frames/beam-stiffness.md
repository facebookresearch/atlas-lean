# Stiffness matrix of an Euler–Bernoulli beam element

For a flexural rigidity `EI` and a length `L` (real numbers), the stiffness matrix of a prismatic
Euler–Bernoulli beam element in the nodal coordinates `(v1, θ1, v2, θ2)` (deflections and rotations
at the two ends), with conjugate end forces, is `K = (EI / L ^ 3) C` where `C` has the rows
`(12, 6L, -12, 6L)`, `(6L, 4L², -6L, 2L²)`, `(-12, -6L, 12, -6L)` and `(6L, 2L², -6L, 4L²)`. It is
defined for all real `EI` and `L`; at `L = 0` it is the zero matrix, by the convention `x / 0 = 0`.
The physical reading is `EI > 0` and `L > 0`.
