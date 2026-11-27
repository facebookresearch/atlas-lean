# Counting descent-compatible cuts

Let `n : ℕ`, `σ ∈ S_n = Equiv.Perm (Fin n)`, and `Des(σ) = {j | j+1<n and σ(j)>σ(j+1)}`. Put
`d = |Des(σ)|`. For every `m : ℕ`, `Fintype.card (CompatibleEulerianCuts σ m) = Nat.choose
(n+m-d) n`.
