# A leading exterior determinant functional

Let `R` be a commutative ring, `M` an `R`-module, and `b : Basis I R M` indexed by a linearly
ordered type `I`. For `n : ℕ` and `s : Set.powersetCard I n`, let `e_s : Fin n ↪o I` enumerate
`s` in order. For `j : I`, define `φ_0=b.coord j` and `φ_(r+1)=b.coord(e_s r)`. The `R`-linear
functional `leadingCoefficient b j s : Λ^(n+1)_R M → R` is the exterior pairing with
`ιMulti_R(φ)`. No condition `j∉s` is imposed.
