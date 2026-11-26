# A missing tail coordinate forces a zero determinant

Let `R` be a commutative ring, `M` an `R`-module, and `b : Basis I R M` indexed by a linearly
ordered type `I`. For `n : ℕ` and `s : Set.powersetCard I n`, let `e_s : Fin n ↪o I` enumerate
`s` in order. Let `j : I`, `s,t : Set.powersetCard I n`, `x : M`, and `r : Fin n`. If `e_t r ∉
s` and `e_t r ≠ j`, then `leadingCoefficient b j s (x ∧ (b.exteriorPower n t))=0`.
