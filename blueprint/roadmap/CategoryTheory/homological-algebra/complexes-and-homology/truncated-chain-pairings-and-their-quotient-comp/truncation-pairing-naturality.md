# Pairing compatibility is preserved by canonical truncation

Let C be an abelian monoidal category with tensor product additive in both variables. Let e be
an embedding of down ℕ into itself which reflects the shape relation and whose image is closed
under incoming arrows (e.IsTruncLE). Let P : K₁ ⊗ K₂ ⟶ K₃ and Q : L₁ ⊗ L₂ ⟶ L₃ be chain
pairings, and let f_i : K_i ⟶ L_i satisfy tensorHom f₁ f₂ ≫ Q = P ≫ f₃. Then tensorHom
(truncLEMap f₁ e) (truncLEMap f₂ e) ≫ truncationPairing e Q = truncationPairing e P ≫ f₃. This
is a map from the tensor of the two truncated K-complexes to L₃.
