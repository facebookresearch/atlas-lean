# The stable-sort fiber cardinality

For `n,m : ℕ` and `σ ∈ S_(n+1)`, `Fintype.card {f : Fin(n+1) → Fin m // Tuple.sort f = σ} =
Nat.choose (n+m-descentNumber σ) (n+1)`.
