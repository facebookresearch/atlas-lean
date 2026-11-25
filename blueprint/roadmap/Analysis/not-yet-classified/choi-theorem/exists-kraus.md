# Finite Kraus representation for complex matrix maps

Let `n` and `m`
be finite index types with decidable equality. Every completely positive map
`phi : Matrix n n ℂ →CP Matrix m m ℂ` has a natural number `k` and a family
`K : Fin k → Matrix m n ℂ` such that `phi = kraus K`; thus
`phi X = ∑ r, K r * X * (K r)ᴴ` for every `X : Matrix n n ℂ`.
Empty input/output index types and `k = 0` remain permitted.
