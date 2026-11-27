# A quotient cochain pulls back by composition with the degree projection

Let R be a commutative ring and equip ModuleCat.{v} R with a monoidal structure additive in
both variables. Let P : K₁ ⊗ K₂ ⟶ K₃ be a pairing of ℕ-indexed chain complexes. Assume K₁.d 1
0 = K₂.d 1 0 = 0, and let Q_P be the chain quotient of K₃ by S_n = positiveImages P n in each
degree, with projection π_P : K₃ ⟶ Q_P. For G : ModuleCat.{v} R, n : ℕ and φ : (Q_P)_n ⟶ G,
the degree-n value of positiveImageCochainInclusion is π_P.f n ≫ φ : K₃.X n ⟶ G.
