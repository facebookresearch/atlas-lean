# The cokernel of the truncated pairing is a chain quotient

Let C be an abelian monoidal category with tensor product additive in both variables. Let e be
an embedding of down ℕ into itself which reflects the shape relation and whose image is closed
under incoming arrows (e.IsTruncLE). For a chain pairing P : K₁ ⊗ K₂ ⟶ K₃, write T_i =
K_i.truncLE e and ι_i : T_i ⟶ K_i for the canonical inclusions. Define truncationQuotient e P
to be the cokernel in ChainComplex C ℕ of tensorHom ι₁ ι₂ ≫ P : T₁ ⊗ T₂ ⟶ K₃.
