# A cochain kills the positive image sum exactly when it kills every component

Let R be a commutative ring and equip ModuleCat.{v} R with a monoidal structure additive in
both variables. Let P : K₁ ⊗ K₂ ⟶ K₃ be a pairing of ℕ-indexed chain complexes. For n : ℕ, G :
ModuleCat.{v} R and φ : K₃.X n ⟶ G, one has positiveImages P n ≤ ker φ.hom if and only if
pairAt P p q n h ≫ φ = 0 for every p > 0, q > 0 and equality h : p + q = n.
