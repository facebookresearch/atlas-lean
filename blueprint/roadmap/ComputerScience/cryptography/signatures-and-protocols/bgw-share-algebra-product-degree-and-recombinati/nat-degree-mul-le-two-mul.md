# Nat Degree mul le two mul

Product of two degree-`t` sharings has degree at most `2 * t`.
`Polynomial.natDegree_mul_le` holds unconditionally, so the zero-polynomial
edge case (`natDegree 0 = 0`) needs no special casing.
