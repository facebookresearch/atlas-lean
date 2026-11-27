# Insertion at the last position

Let `n : ℕ`, `i : Fin(n+1)`, and `π : Equiv.Perm (Fin n)`. Write `ν_i(j) = i.succAbove j` for
the increasing embedding that omits `i`. `orderedLast i π = orderedFirst i π *
finRotate(n+1)`. It sends the last position to `i` and each `j.castSucc` to `ν_i(π j)`, with
permutation multiplication `(p*q)(j) = p(q(j))`.
