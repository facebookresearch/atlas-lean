# Norm bound for a block-encoded matrix

If `U` is an `(α, ε)` block-encoding of the matrix `A` with ancilla register
`κ` and reference vector `o`, then `‖A‖ ≤ α + ε`.

Here `ι`, `κ`, `μ` are finite types, matrices are complex, `‖·‖` is the
operator norm induced by the Euclidean norm, and `IsBlockEncoding A α ε o U`
means that `U` is a unitary matrix on `κ × ι`, that `‖A - α • ancillaBlock o
U‖ ≤ ε`, and that `α ≥ 0` and `ε ≥ 0`.
