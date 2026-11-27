# The leading coefficient has a determinant matrix

Let `R` be a commutative ring, `M` an `R`-module, and `b : Basis I R M` indexed by a linearly
ordered type `I`. For `n : ℕ` and `s : Set.powersetCard I n`, let `e_s : Fin n ↪o I` enumerate
`s` in order. For `j : I` and `a : Fin(n+1) → M`, `leadingCoefficient b j s (ιMulti_R
a)=det(φ_k(a_i))`, with `φ_0=b.coord j` and `φ_(r+1)=b.coord(e_s r)`. Rows index input vectors
and columns index these dual coordinates.
