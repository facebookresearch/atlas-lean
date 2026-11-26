# Closing-cut coordinates are rotation values

Let `n : ℕ`, `N=n+1`, and `ρ=finRotate N`. Addition and negation on `Fin N` are taken modulo
`N`. For `r : Fin N`, `closingCutEquiv n r = (ρ^r.val)(Fin.last n)`.
