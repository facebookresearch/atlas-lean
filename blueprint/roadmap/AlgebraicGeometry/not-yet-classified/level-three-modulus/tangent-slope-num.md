# Numerator of the tangent-slope quotient

For a Weierstrass curve $W$ and $x, y$,
`W.tangentSlopeNum x y` is $3x^2 + 2a_2x + a_4 - a_1y$, the numerator of `tangentSlope`. It is
minus the partial derivative in $x$ of the Weierstrass polynomial at $(x, y)$
(`tangentSlopeNum_eq_neg_evalEval_polynomialX`).
