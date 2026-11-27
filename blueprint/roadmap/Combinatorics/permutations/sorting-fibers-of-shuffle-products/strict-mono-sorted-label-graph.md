# The sorted label graph is strictly increasing

For `n,m : ℕ` and `f : Fin n → Fin m`, the function `i ↦ toLex(f(Tuple.sort f i), Tuple.sort f
i)` is strictly increasing. Equal labels are therefore ordered by their input indices.
