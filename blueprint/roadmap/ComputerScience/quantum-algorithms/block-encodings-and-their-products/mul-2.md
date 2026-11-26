# Product of qubit block-encodings

Let `U` on `a + s` qubits be an `(α, δ)` qubit block-encoding of the
`s`-qubit matrix `A`, and let `V` on `b + s` qubits be a `(β, ε)` qubit
block-encoding of `B`, with `α ≥ 0` and `β ≥ 0`. Then `ancillaMul U V`, with
its two ancilla registers merged into one register of `a + b` qubits by
`qubitAncillaEquiv a b`, is an `(α * β, α * ε + β * δ + δ * ε)` qubit
block-encoding of `A * B` with `a + b` ancilla qubits.

A qubit block-encoding uses the reference ancilla vector `|0⟩`; norms are
operator norms. This is Lemma 53 of Gilyén, Su, Low and Wiebe
(arXiv:1806.01838) in qubit form, with the cross term `δ * ε` in the error.
