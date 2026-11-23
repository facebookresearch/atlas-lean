# Single crossing (Levin and Reeds 1977, Theorem 2)

At an overdispersed sample
(`0 < M < V`), once the profile shape score is `≤ 0` at some `a > 0`, it is `< 0` at every larger
shape. The proof writes the score as `H(T) / (a + T)² + 2 ∫₀ᵀ H(u) / (a + u)³ du`
(`profileShapeScore_eq_integral`), uses the single sign change of `H` at `u*`
(`smoothedDiscrepancy_neg_of_le`), and shows `a ↦ (a + u*)³ · profileShapeScore a k` strictly
decreasing: the kernel `((a + u*) / (a + u))³` is decreasing in `a` where `H ≥ 0` (`u ≤ u*`) and
increasing where `H ≤ 0`, and `H(T) = n (M - V) / 2 < 0` makes the boundary term strict.
