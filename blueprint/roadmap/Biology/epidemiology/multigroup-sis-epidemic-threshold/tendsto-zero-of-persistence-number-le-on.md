# Lajmanovich–Yorke theorem, die-out

Theorem 3.1 of Hethcote and Yorke (1984), after
Lajmanovich and Yorke (1976): let the index set `ι` of groups be finite and nonempty, let `C` be a
contact matrix with every `C_ij ≥ 0` that is irreducible or has a single group, and let `e` be
recovery rates with every `e_i > 0`. If the persistence number satisfies
`R₀ = LevinsNetwork.persistenceNumber C e ≤ 1` (the critical case `R₀ = 1` included; equivalently
`s(A) ≤ 0` in Lajmanovich and Yorke's notation), then every solution `I` of
`LevinsNetwork.IsSolution C e I` with `I 0 ∈ [0, 1]ⁿ` tends to `0`. The source asks only that the
population cannot be split into two parts that do not contact each other. A single group cannot
be split even when `C = 0`, which `Matrix.IsIrreducible` excludes, since it asks for a path of
positive length from each group to itself.
