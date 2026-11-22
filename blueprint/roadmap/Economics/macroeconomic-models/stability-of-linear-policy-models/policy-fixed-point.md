# Candidate fixed point of the affine policy iteration

The candidate fixed point of the affine policy iteration, solved
explicitly from the triangular system (`x*_2 = c_2 / (1 - d)`, then
`x*_1 = (c_1 + b x*_2) / (1 - a)`). It satisfies `x* = A x* + c` when
`a ≠ 1` and `d ≠ 1` (see `linearPolicyMatrix_mulVec_fixedPoint_add`); no
uniqueness is claimed here.
