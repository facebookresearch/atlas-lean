# Qubit block-encoding

For a complex matrix `A` on `s` qubits (indexed by `Fin (2 ^ s)`), reals `α`
and `ε`, and a complex matrix `U` indexed by `Fin (2 ^ a) × Fin (2 ^ s)` (an
`a`-qubit ancilla register followed by the `s` system qubits),
`IsQubitBlockEncoding A α ε U` is the block-encoding condition with
reference ancilla vector `|0^a⟩`: `U` is unitary, `‖A - α • ancillaBlock 0
U‖ ≤ ε` in the operator norm, `α ≥ 0` and `ε ≥ 0`. This is the qubit form of
Definition 43 of Gilyén, Su, Low and Wiebe (arXiv:1806.01838).
