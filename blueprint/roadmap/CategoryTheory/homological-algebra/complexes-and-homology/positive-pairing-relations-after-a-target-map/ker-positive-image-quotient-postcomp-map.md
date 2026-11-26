# The quotient-map kernel is the image of the ambient target-map kernel

Let R be a ring and equip ModuleCat.{v} R with a monoidal structure additive in both
variables. Let P : K₁ ⊗ K₂ ⟶ K₃ be a chain pairing of ℕ-indexed chain complexes. Let f : K₃ ⟶
L be a chain map and write S_n for positiveImages P n. Assume K₁.d 1 0 = 0 and K₂.d 1 0 = 0,
so these image families define quotient complexes. For n : ℕ, the kernel of the induced degree
quotient map equals (LinearMap.ker (f.f n).hom).map S_n.mkQ. As a submodule of K₃.X n/S_n, it
is (ker f_n + S_n)/S_n.
