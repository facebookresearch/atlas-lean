# One-ancilla encoding of a projection

For a complex matrix `P` on a finite type `ι`, `projEncoding P` is the
matrix `X ⊗ (1 - P) + 1 ⊗ P` on `Fin 2 × ι`: its entry at `((b, i), (b',
j))` is `P i j` when `b = b'` and `(1 - P) i j` otherwise. Its ancilla block
at `0` is `P`, and it is unitary when `P` is an orthogonal projection.
