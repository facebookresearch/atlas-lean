# Every permutation has rotation and tail coordinates

Let `n : ℕ`, `N=n+1`, and `ρ=finRotate N`. Addition and negation on `Fin N` are taken modulo
`N`. `rotationHeadEquiv n : Fin N × S_n ≃ S_N` sends `(r,π)` to `ρ^r.val * headFixingHom n π`.
The inverse records the first value and the tail permutation after rotating that value to
zero.
