# Global existence and uniqueness

Lajmanovich and Yorke (1976), as restated by Hethcote
and Yorke (1984, p. 27): on a finite index set `ι` of groups, let `C` be a contact matrix with
every `C_ij ≥ 0` and `e` recovery rates with every `e_i > 0` (for the multigroup SIS model,
`C_ij = λ_ij N_j / N_i` and `e_i = 1 / d_i`). For every initial state `I₀ ∈ [0, 1]ⁿ` there is a
solution `I` of `I' = LevinsNetwork.field C e I` on `[0, ∞)` (`LevinsNetwork.IsSolution C e I`)
with `I 0 = I₀`; it stays in `[0, 1]ⁿ`, and every solution `J` with `J 0 = I₀` agrees with `I`
for all `t ≥ 0`. This is the source's well-posedness without its continuous dependence on the
initial data, which is not stated here.
