# A pairing component with an explicit target-degree equality

Let R be a ring and equip ModuleCat.{v} R with a monoidal structure additive in both
variables. Let P : K₁ ⊗ K₂ ⟶ K₃ be a chain pairing of ℕ-indexed chain complexes. For p, q, n :
ℕ and h : p + q = n, define pairAt P p q n h : K₁.X p ⊗ K₂.X q ⟶ K₃.X n as the tensor-complex
coprojection in total degree n followed by P.f n.
