# A zero tail coordinate isolates the leading coefficient

Let `R` be a commutative ring, `M` an `R`-module, and `b : Basis I R M` indexed by a linearly
ordered type `I`. For `n : ℕ` and `s : Set.powersetCard I n`, let `e_s : Fin n ↪o I` enumerate
`s` in order. Let `j : I`, `x : M`, and `a : Fin n → M` satisfy `b.coord j (a i)=0` for all
`i`. Then `leadingCoefficient b j s (ιMulti_R(Fin.cons x a)) = b.coord j x * ιMultiDual R n b
s (ιMulti_R a)`.
