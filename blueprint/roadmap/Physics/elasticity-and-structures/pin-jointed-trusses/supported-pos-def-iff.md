# Supported pos Def iff

Support-restriction rigidity certificate: for positive
member stiffnesses `k`, the supported stiffness
`(B S)ᵀ diag(k) (B S)` is positive definite iff the
supported compatibility map `B S` has trivial kernel (no
generalized-coordinate null mode). For arbitrary `S` a
kernel vector `u` need not give a nonzero joint
displacement `S *ᵥ u`; the physical supported-mechanism
reading needs `S.mulVec` injective, as for a coordinate
selection. Connectivity of the member graph is not
assumed and does not suffice. This is the weighted-Gram
characterization
`MetaMathlibExt.posDef_mul_diagonal_mul_transpose_iff`
at the supported compatibility map.
