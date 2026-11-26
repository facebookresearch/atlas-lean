# A truncated component is the pairing after the component inclusions

Let C be an abelian monoidal category with tensor product additive in both variables. Let e be
an embedding of down ℕ into itself which reflects the shape relation and whose image is closed
under incoming arrows (e.IsTruncLE). For a chain pairing P : K₁ ⊗ K₂ ⟶ K₃, write T_i =
K_i.truncLE e and ι_i : T_i ⟶ K_i for the canonical inclusions. For p, q : ℕ, pair
(truncationPairing e P) p q = (ι₁.f p ⊗ₘ ι₂.f q) ≫ pair P p q as a morphism T₁.X p ⊗ T₂.X q ⟶
K₃.X (p + q).
