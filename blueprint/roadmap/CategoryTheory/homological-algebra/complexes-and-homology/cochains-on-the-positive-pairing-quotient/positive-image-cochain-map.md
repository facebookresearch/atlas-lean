# A compatible map of pairings pulls quotient cochains back

Let R be a commutative ring and equip ModuleCat.{v} R with a monoidal structure additive in
both variables. Let P : K₁ ⊗ K₂ ⟶ K₃ be a pairing of ℕ-indexed chain complexes. Assume K₁.d 1
0 = K₂.d 1 0 = 0, and let Q_P be the chain quotient of K₃ by S_n = positiveImages P n in each
degree, with projection π_P : K₃ ⟶ Q_P. Let Q : L₁ ⊗ L₂ ⟶ L₃ be another pairing with L₁.d 1 0
= L₂.d 1 0 = 0. Let f_i : K_i ⟶ L_i satisfy tensorHom f₁ f₂ ≫ Q = P ≫ f₃, and write q(f) : Q_P
⟶ Q_Q for the induced quotient map. For G : ModuleCat.{v} R, precomposition with q(f) defines
positiveImageCochainMap : Hom_R(Q_Q, G) ⟶ Hom_R(Q_P, G). Its direction is contravariant in the
quotient chain map.
