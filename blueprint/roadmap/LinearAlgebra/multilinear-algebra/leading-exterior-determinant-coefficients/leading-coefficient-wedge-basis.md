# Leading coefficients distinguish an omitted-index basis word

Let `R` be a commutative ring, `M` an `R`-module, and `b : Basis I R M` indexed by a linearly
ordered type `I`. For `n : ℕ` and `s : Set.powersetCard I n`, let `e_s : Fin n ↪o I` enumerate
`s` in order. Let `s,t` have cardinality `n`, `j∉t`, and `x : M`. Then `leadingCoefficient b j
s (x ∧ (b.exteriorPower n t)) = if s=t then b.coord j x else 0`.
