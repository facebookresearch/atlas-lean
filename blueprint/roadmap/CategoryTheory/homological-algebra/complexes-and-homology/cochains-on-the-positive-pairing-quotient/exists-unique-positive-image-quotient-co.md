# Annihilation of positive components is equivalent to a unique quotient cochain

Let R be a commutative ring and equip ModuleCat.{v} R with a monoidal structure additive in
both variables. Let P : K₁ ⊗ K₂ ⟶ K₃ be a pairing of ℕ-indexed chain complexes. Assume K₁.d 1
0 = K₂.d 1 0 = 0, and let Q_P be the chain quotient of K₃ by S_n = positiveImages P n in each
degree, with projection π_P : K₃ ⟶ Q_P. For n : ℕ, G : ModuleCat.{v} R and φ : K₃.X n ⟶ G,
there exists a unique ψ : (Q_P)_n ⟶ G with π_P.f n ≫ ψ = φ if and only if pairAt P p q n h ≫ φ
= 0 for every p > 0, q > 0 and h : p + q = n.
