# For admissible angles, the triclinic lattice

For `a, b, c > 0` and angles `α`, `β`, `γ` with `sin γ ≠ 0` and
`Ω = 1 - cos² α - cos² β - cos² γ + 2 cos α cos β cos γ > 0`, the triclinic lattice (Pearson symbol
`aP`) is the [Bravais lattice](../bravais-lattices/bravais-lattice.md) whose primitive vectors
(columns of the basis matrix) are `(a, 0, 0)`, `(b cos γ, b sin γ, 0)` and
`(c cos β, c (cos α - cos β cos γ) / sin γ, c √Ω / sin γ)`. These have lengths `a`, `b`, `c`, and
the dot products of the second and third, the first and third and the first and second are
`b c cos α`, `a c cos β` and `a b cos γ`. So the angles between them are `arccos(cos α)`,
`arccos(cos β)` and `arccos(cos γ)`: when `α`, `β` and `γ` lie in `(0, π)`, `α` is the angle between
the second and third vectors, `β` between the first and third and `γ` between the first and second.
The hypotheses make the divisions and the square root meaningful and the determinant nonzero.
