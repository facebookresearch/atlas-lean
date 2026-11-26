# The last position contains the distinguished value

Let `n : ℕ`, `i : Fin(n+1)`, and `π : Equiv.Perm (Fin n)`. Write `ν_i(j) = i.succAbove j` for
the increasing embedding that omits `i`. The last-position value is `orderedLast i π (Fin.last
n) = i`.
