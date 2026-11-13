# Perron root of a Leslie matrix

If the Leslie matrix is irreducible (for example under
`isIrreducible_leslieMatrix`), the Perron–Frobenius theorem
`Matrix.IsIrreducible.perron_frobenius` gives a positive eigenvalue `r` with a positive
eigenvector that dominates every complex eigenvalue in modulus; since `r > 0` and `v 0 > 0`,
`r` satisfies the discrete Euler–Lotka equation. Nothing here asserts convergence of normalized
iterates `L^t v₀` (that needs primitivity and is not proved).
