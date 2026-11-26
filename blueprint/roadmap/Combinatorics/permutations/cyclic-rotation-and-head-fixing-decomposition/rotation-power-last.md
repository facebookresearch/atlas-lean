# The rotated closing position is last plus index

Let `n : ℕ`, `N=n+1`, and `ρ=finRotate N`. Addition and negation on `Fin N` are taken modulo
`N`. For `r : Fin N`, `(ρ^r.val)(Fin.last n) = Fin.last n + r`.
