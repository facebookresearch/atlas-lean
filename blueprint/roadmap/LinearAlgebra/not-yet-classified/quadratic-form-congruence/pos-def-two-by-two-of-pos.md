# Pos Def two by two of pos

Explicit constitutive inequalities for a symmetric `2 × 2` matrix: if `0 < a` and
`0 < a * d - b ^ 2`, then `!![a, b; b, d]` is positive definite. The two inequalities say that the
leading principal minors `a` and `a * d - b ^ 2 = det` are positive, so this is the `2 × 2`
instance of the sufficiency direction of the ATLAS Sylvester criterion
`Matrix.posDef_iff_leadingPrincipalMinors_pos`. That module is not imported; the proof completes
the square in the expansion `quadForm_two_by_two` instead.
