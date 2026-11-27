# Postcomposition takes the relation submodule to its direct image

Let R be a ring and equip ModuleCat.{v} R with a monoidal structure additive in both
variables. Let P : K₁ ⊗ K₂ ⟶ K₃ be a chain pairing of ℕ-indexed chain complexes. Let f : K₃ ⟶
L be a chain map and write S_n for positiveImages P n. For every n : ℕ, positiveImages
(P.postcomp f) n = S_n.map (f.f n).hom.
