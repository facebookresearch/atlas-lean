# Simultaneous diagonalization

Commuting Hermitian matrices `A` and `B` share an
orthonormal eigenbasis: one unitary matrix `U` diagonalizes both, with real eigenvalues. The
joint eigenspaces of their Euclidean operators are mutually orthogonal and span the space, by
Mathlib's `LinearMap.IsSymmetric.directSum_isInternal_of_commute` and
`LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace`; the columns of `U` are an
orthonormal basis subordinate to that decomposition.
