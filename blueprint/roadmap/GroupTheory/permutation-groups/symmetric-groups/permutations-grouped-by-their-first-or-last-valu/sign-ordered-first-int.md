# The integer sign of first insertion

Let `n : ℕ`, `i : Fin(n+1)`, and `π : Equiv.Perm (Fin n)`. Write `ν_i(j) = i.succAbove j` for
the increasing embedding that omits `i`. After coercing signs to `ℤ`, `((orderedFirst i
π).sign : ℤ) = (-1 : ℤ)^i.val * (π.sign : ℤ)`.
