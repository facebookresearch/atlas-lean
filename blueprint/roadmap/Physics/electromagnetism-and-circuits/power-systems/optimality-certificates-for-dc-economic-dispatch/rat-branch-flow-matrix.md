# Rational branch-flow coefficient matrix

For a network with rational susceptances `b`, the rational branch-flow matrix is `diag(b) Bᵀ`, with
`B` the [rational incidence matrix](rat-incidence.md). The rational objects copy the real ones
entrywise, so that the checker is computable; the [casting lemmas](rat-lp-matrix-map.md) identify
them with the real linear program.
