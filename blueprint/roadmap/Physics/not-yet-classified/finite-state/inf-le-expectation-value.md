# Inf' le expectation Value

Variational bound: if `A = U * diagonal d * Uᴴ` with `U` unitary and `d` real, then for every
normalized state `ψ` the expectation value of `A` is at least the smallest entry
`Finset.univ.inf' Finset.univ_nonempty d` of `d`. The decomposition is an explicit hypothesis; such
an `A` is Hermitian (`Matrix.isHermitian_mul_mul_conjTranspose`), and Mathlib's spectral theorem
provides the decomposition for every Hermitian matrix (`inf'_eigenvalues_le_expectationValue`).
