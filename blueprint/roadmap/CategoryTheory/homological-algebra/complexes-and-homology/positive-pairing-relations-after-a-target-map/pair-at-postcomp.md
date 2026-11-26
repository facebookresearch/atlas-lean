# A postcomposed pairing component is the component followed by the target map

Let R be a ring and equip ModuleCat.{v} R with a monoidal structure additive in both
variables. Let P : K₁ ⊗ K₂ ⟶ K₃ be a chain pairing of ℕ-indexed chain complexes. Let f : K₃ ⟶
L be a chain map and write S_n for positiveImages P n. For p + q = n with equality h, pairAt
(P.postcomp f) p q n h = pairAt P p q n h ≫ f.f n.
