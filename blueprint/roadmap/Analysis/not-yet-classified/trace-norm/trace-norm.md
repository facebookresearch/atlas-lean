# Trace Norm

Trace norm of a finite square complex matrix, defined as the sum of
singular values of its associated linear map `Matrix.toEuclideanLin`.
We sum over `Finset.range (Fintype.card n)`, which contains all possibly
nonzero singular values for an `n × n` matrix.

Here `n` is any finite index type with decidable equality. The matrices are arbitrary square
complex matrices, and the empty-index case is included.
