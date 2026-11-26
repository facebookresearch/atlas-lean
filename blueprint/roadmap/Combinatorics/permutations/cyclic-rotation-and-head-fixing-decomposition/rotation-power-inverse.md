# Inverse rotation uses the negative finite index

Let `n : ℕ`, `N=n+1`, and `ρ=finRotate N`. Addition and negation on `Fin N` are taken modulo
`N`. For `r : Fin N`, `(ρ^r.val)⁻¹ = ρ^(-r).val`, where `-r` is modular negation in `Fin N`.
