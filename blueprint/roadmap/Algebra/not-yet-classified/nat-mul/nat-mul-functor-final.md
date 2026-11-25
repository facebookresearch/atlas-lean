# Nat Mul Functor final

The functor `n ↦ n * k` is final when `0 < k`.

The positivity hypothesis `hk : 0 < k` gives `∀ n, n ≤ n * k` via
`Nat.le_mul_of_pos_right`, which is exactly the finality criterion for
monotone maps `ℕ → ℕ` through `Monotone.final_functor_iff`.
