# Grounded Angles

Grounded DC angles: solve the non-reference equations `L_b θ = p` with the reduced grounded
matrix and reconstruct the reference angle `θ ref = 0`. The matrix inverse is Mathlib's
`Matrix.inv`, which is the true inverse when the reduced matrix is invertible.
