# A compatible triple of chain maps induces a truncated-quotient map

Let C be an abelian monoidal category with tensor product additive in both variables. Let e be
an embedding of down ℕ into itself which reflects the shape relation and whose image is closed
under incoming arrows (e.IsTruncLE). Let P : K₁ ⊗ K₂ ⟶ K₃ and Q : L₁ ⊗ L₂ ⟶ L₃ be chain
pairings, and let f_i : K_i ⟶ L_i satisfy tensorHom f₁ f₂ ≫ Q = P ≫ f₃. The resulting
commutative square induces truncationQuotientMap : truncationQuotient e P ⟶ truncationQuotient
e Q by the cokernel map, using the tensor of the truncated f₁ and f₂ on the source and f₃ on
the target.
