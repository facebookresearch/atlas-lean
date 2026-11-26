# The last-value equivalence is ordered insertion

Let `n : ℕ`, `i : Fin(n+1)`, and `π : Equiv.Perm (Fin n)`. Write `ν_i(j) = i.succAbove j` for
the increasing embedding that omits `i`. `orderedLastEquiv n (i,π) = orderedLast i π`.
