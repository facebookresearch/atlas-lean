# An omitted basis index kills every left-wedge coordinate

Let `R` be a commutative ring, `M` an `R`-module, and `b : Basis I R M` a basis indexed by a
linearly ordered type `I`. Let `n : ℕ`, `s : Set.powersetCard I (n+1)`, `i ∉ s`, and `x :
Λ^n_R M`. Then `(b.exteriorPower(n+1)).repr (wedgeLeft R M (b i) n x) s = 0`.
