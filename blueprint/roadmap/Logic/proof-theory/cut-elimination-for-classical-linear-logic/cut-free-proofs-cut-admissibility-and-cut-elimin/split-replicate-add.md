# Splitting replicated copies across a sum of sequents

Given `Multiset.replicate n a + Γ = (Δ : Sequent) + Θ`, split the `n` copies of `a`
between `Δ` and `Θ`, returning counts `k` and `l` and residual lists.
