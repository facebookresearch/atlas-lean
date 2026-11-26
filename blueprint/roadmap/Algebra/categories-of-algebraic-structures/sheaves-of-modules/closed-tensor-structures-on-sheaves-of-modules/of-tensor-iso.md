# Tensor comparison for sheaf restriction

Let `(C,J,R)` be a commutative ringed site at universe `u`, with weak additive sheafification,
monoidal `W`, and locally-bijective and underlying-ring comparisons on the base and slice over
`X`. For `F=restrictSheaf R X` and module sheaves `M,N`, `ofTensorIso R X M N : F(M ⊗ N) ≅
F(M) ⊗ F(N)` is the inverse of `Functor.Monoidal.μIso F M N`.
