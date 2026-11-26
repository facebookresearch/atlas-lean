# Merging two qubit ancilla registers

For natural numbers `a` and `b`, `qubitAncillaEquiv a b` is the bijection
`Fin (2 ^ b) × Fin (2 ^ a) ≃ Fin (2 ^ (a + b))` given by the standard
product equivalence `Fin m × Fin n ≃ Fin (m * n)` followed by `2 ^ b * 2 ^ a
= 2 ^ (a + b)`. It sends `(0, 0)` to `0`.
