# Removing descent rises is a labeling equivalence

Let `n,m : ℕ`, `σ ∈ S_(n+1)`, and `d = descentNumber σ < m`. There is an equivalence
`DescentLabeling σ m ≃ {h : Fin(n+1) → Fin(m-d) // Monotone h}`. It sends `g_i` to the finite
index with value `g_i.val - descentPrefix σ i`; its inverse adds the same prefix.
