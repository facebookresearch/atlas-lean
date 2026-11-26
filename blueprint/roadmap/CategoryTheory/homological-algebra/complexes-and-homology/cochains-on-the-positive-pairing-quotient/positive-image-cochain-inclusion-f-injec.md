# Pullback of quotient cochains is injective in every degree

Let R be a commutative ring and equip ModuleCat.{v} R with a monoidal structure additive in
both variables. Let P : K₁ ⊗ K₂ ⟶ K₃ be a pairing of ℕ-indexed chain complexes. Assume K₁.d 1
0 = K₂.d 1 0 = 0, and let Q_P be the chain quotient of K₃ by S_n = positiveImages P n in each
degree, with projection π_P : K₃ ⟶ Q_P. For every G : ModuleCat.{v} R and n : ℕ, the degree-n
map Hom_R((Q_P)_n, G) → Hom_R(K₃.X n, G) given by precomposition with π_P.f n is injective.
