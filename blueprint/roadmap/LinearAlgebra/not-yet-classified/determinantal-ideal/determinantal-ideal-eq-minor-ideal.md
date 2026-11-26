# Determinantal ideals in ordered finite bases

Let `R` be a commutative ring and `M,N` be `R`-modules. Let `bM,bN` be bases
indexed by finite types `ι,κ`, each equipped with a linear order. For every
`r : ℕ` and linear map `f : M →ₗ[R] N`,

`f.determinantalIdeal r = Matrix.minorIdeal r (LinearMap.toMatrix bM bN f)`.

Rows use target-basis indices `κ` and columns source-basis indices `ι`, with
their specified orders.
