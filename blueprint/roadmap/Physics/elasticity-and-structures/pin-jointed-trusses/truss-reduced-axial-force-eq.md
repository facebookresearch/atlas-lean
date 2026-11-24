# Truss reduced axial Force eq

Physical axial forces from the separation-form
coefficients: with the same data as
`truss_reduced_memberCoefficient_eq_inv_mulVec`, the
physical axial force vector `fun e => s e * L e` (member
length times the separation-form coefficient
`s = Matrix.diagonal k *ᵥ ((B S) *ᵥ u)`, tension positive)
is the memberwise length rescaling of the reduced statics
coefficient solution. In particular the physical forces,
like the coefficients, do not depend on the axial
weights `k` through anything but the common statics
solution.
