# The Lyapunov matrix and the identity are positive definite

The [Lyapunov matrix](longitudinal-lyapunov-matrix.md) `P` and the identity matrix `Q = 1` of
size `4` are symmetric positive definite. For `P` this follows from
[Sylvester's criterion](../../../../LinearAlgebra/positive-definite-matrices/sylvester-s-criterion/pos-def-iff-leading-principal-minors-pos.md):
its leading principal minors are `1/2`, `1/4`, `3/8` and `1/8`, the last being `1/4` times the
determinant `1/2` of the pitch block.
