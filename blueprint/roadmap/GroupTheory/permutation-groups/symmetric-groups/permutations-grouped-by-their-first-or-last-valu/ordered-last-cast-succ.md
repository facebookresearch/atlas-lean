# The initial positions use ordered deletion

Let `n : ℕ`, `i : Fin(n+1)`, and `π : Equiv.Perm (Fin n)`. Write `ν_i(j) = i.succAbove j` for
the increasing embedding that omits `i`. For `j : Fin n`, `orderedLast i π j.castSucc = ν_i(π
j)`.
