# Monomial Equiv

Heterogeneous monomial equivalence: for `u : m → Rˣ` and `σ : n ≃ m`,
the matrix with entry `u i` at `(i, σ⁻¹ i)` and `0` elsewhere, i.e.
`val i j = if σ j = i then (u i : R) else 0`.

Its inverse has entry `(u j)⁻¹` at `(σ⁻¹ j, j)`. Implemented as
`diagonal u * (σ⁻¹).toPEquiv.toMatrix`.
