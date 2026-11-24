# Map embedding Down Nat To Int Extend

Zero-extension from `ChainComplex C ℕ` to `ChainComplex C ℤ` preserves short exactness.

This is the specialization of `map_extendFunctor` to the embedding
`ComplexShape.embeddingDownNatToInt`.  The wrapper functor
`ComplexShape.embeddingDownNatToIntExtendFunctor` is definitionally the same
as `ComplexShape.embeddingDownNatToInt.extendFunctor`, so the result follows
directly from the generic theorem.
