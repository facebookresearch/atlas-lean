# The sign of last insertion

Let `n : ℕ`, `i : Fin(n+1)`, and `π : Equiv.Perm (Fin n)`. Write `ν_i(j) = i.succAbove j` for
the increasing embedding that omits `i`. In `ℤˣ`, `(orderedLast i π).sign = (-1)^n *
((-1)^i.val * π.sign)`.
