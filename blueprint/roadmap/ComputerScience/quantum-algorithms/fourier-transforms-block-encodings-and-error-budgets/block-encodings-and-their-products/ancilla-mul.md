# Product unitary of two block-encodings

For finite types `κ`, `μ`, `ι`, a complex matrix `U` on `κ × ι` and a
complex matrix `V` on `μ × ι`, `ancillaMul U V` is the matrix `(I_μ ⊗ U)(I_κ
⊗ V)` on `(μ × κ) × ι`, with both factors reindexed to `(μ × κ) × ι`: `V`
acts on `μ × ι` first, then `U` acts on `κ × ι`, each as the identity on the
other ancilla register.
