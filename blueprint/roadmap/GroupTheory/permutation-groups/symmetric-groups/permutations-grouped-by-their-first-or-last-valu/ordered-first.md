# Insertion at the first position

Let `n : ℕ`, `i : Fin(n+1)`, and `π : Equiv.Perm (Fin n)`. Write `ν_i(j) = i.succAbove j` for
the increasing embedding that omits `i`. `orderedFirst i π` is the permutation of `Fin(n+1)`
determined by `orderedFirst i π 0 = i` and `orderedFirst i π j.succ = ν_i(π j)` for `j : Fin
n`.
