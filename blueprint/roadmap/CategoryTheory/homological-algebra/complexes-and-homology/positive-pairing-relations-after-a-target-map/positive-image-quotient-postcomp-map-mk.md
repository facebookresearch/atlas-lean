# The descended map sends a class to the class of its image

Let R be a ring and equip ModuleCat.{v} R with a monoidal structure additive in both
variables. Let P : K₁ ⊗ K₂ ⟶ K₃ be a chain pairing of ℕ-indexed chain complexes. Let f : K₃ ⟶
L be a chain map and write S_n for positiveImages P n. Assume K₁.d 1 0 = 0 and K₂.d 1 0 = 0,
so these image families define quotient complexes. For every n : ℕ and x : K₃.X n, the
degree-n quotient map sends S_n.mkQ x to (positiveImages (P.postcomp f) n).mkQ ((f.f n).hom
x).
