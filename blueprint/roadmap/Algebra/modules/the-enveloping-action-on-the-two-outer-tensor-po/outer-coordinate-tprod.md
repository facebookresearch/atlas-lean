# The outer coordinate keeps the middle tensor word

Let `k` be a commutative semiring and `A` a `k`-semimodule. For `n : ℕ`, `a₀ : A`, and `a :
Fin(n+1) → A`, the map sends `a₀ ⊗ tprod(a)` to `(a₀ ⊗ op(a(Fin.last n))) ⊗ tprod(Fin.init
a)`.
