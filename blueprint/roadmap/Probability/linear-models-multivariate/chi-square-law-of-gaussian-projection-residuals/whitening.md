# Whitening matrix

For a real square matrix `V` indexed by a finite set, the whitening matrix is `W = (√V)⁻¹`, the
inverse of the square root `√V` of `V` given by the continuous functional calculus. For positive
definite `V`, `√V` is the positive definite square root of `V` and `W` is its inverse, so that
`W W = V⁻¹`. The definition is total: the square root of a matrix that is not positive semidefinite
is `0`, and the inverse of a singular matrix is `0`, so `W = 0` whenever `V` is not positive
definite. The intended domain is positive definite `V`.
