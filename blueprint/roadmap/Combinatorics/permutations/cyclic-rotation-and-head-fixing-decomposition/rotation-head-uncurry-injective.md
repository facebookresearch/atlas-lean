# Rotation and tail coordinates determine the permutation

Let `n : ℕ`, `N=n+1`, and `ρ=finRotate N`. Addition and negation on `Fin N` are taken modulo
`N`. The function `(r,π) ↦ ρ^r.val * headFixingHom n π` from `Fin N × S_n` to `S_N` is
injective. The first value recovers `r` and the remaining fixed-head action recovers `π`.
