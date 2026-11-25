# Product of block-encodings

Let `U` be an `(α, δ)` block-encoding of `A` with ancilla register `κ` and
reference vector `oκ`, and let `V` be a `(β, ε)` block-encoding of `B` with
ancilla register `μ` and reference vector `oμ`, where `α ≥ 0` and `β ≥ 0`.
Then the product unitary `ancillaMul U V` on `(μ × κ) × ι` is an `(α * β, α
* ε + β * δ + δ * ε)` block-encoding of `A * B` with reference vector `(oμ,
oκ)`.

Here `ι`, `κ`, `μ` are finite types, matrices are complex, `‖·‖` is the
operator norm induced by the Euclidean norm, and `IsBlockEncoding A α ε o U`
means that `U` is a unitary matrix on `κ × ι`, that `‖A - α • ancillaBlock o
U‖ ≤ ε`, and that `α ≥ 0` and `ε ≥ 0`. The bound is that of Lemma 53 of
Gilyén, Su, Low and Wiebe (arXiv:1806.01838) together with the cross term `δ
* ε`.
