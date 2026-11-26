# The sorted label graph with stable ties

For `n,m : ℕ` and `f : Fin n → Fin m`, put `s_f = Tuple.sort f`. The graph labeling
`sortedLabelGraph f : Fin n → Fin m ×ₗ Fin n` is `i ↦ toLex(f(s_f i), s_f i)`, ordering labels
first and input indices second.
