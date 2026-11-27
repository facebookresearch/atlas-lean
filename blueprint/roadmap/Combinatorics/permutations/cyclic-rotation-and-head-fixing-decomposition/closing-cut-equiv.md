# The closing-cut coordinate equivalence

Let `n : ℕ`, `N=n+1`, and `ρ=finRotate N`. Addition and negation on `Fin N` are taken modulo
`N`. `closingCutEquiv n : Fin N ≃ Fin N` is modular translation `r ↦ Fin.last n + r`, with
inverse translation by `-Fin.last n`.
