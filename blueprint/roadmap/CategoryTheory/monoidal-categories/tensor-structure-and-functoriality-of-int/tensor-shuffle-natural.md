# Tensor Shuffle natural

In a symmetric monoidal category, the isomorphism `tensorShuffle A B U V : (A ⊗ B) ⊗ (V ⊗ U) ≅ (A ⊗ U) ⊗ (B ⊗ V)` is natural in all four objects: for morphisms `a : A ⟶ A'`, `b : B ⟶ B'`, `u : U ⟶ U'` and `v : V ⟶ V'`, applying `(a ⊗ b) ⊗ (v ⊗ u)` and then the shuffle equals the shuffle followed by `(a ⊗ u) ⊗ (b ⊗ v)`.
