# The integer sign of last insertion

Let `n : ℕ`, `i : Fin(n+1)`, and `π : Equiv.Perm (Fin n)`. Write `ν_i(j) = i.succAbove j` for
the increasing embedding that omits `i`. After coercing signs to `ℤ`, `((orderedLast i π).sign
: ℤ) = (-1 : ℤ)^n * ((-1 : ℤ)^i.val * (π.sign : ℤ))`.
