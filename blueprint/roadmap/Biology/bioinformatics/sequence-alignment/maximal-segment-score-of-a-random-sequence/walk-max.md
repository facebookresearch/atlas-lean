# Walk Max

The **maximum of the score walk** `max_{0 ≤ k ≤ n} S_k` of a score list `x₀, …, x_{n-1}`,
where `S_k = x₀ + ⋯ + x_{k-1}` and `S₀ = 0`: the largest sum of a (possibly empty) prefix
(`sum_le_walkMax_of_prefix`, `exists_prefix_sum_eq_walkMax`). Computed by the first-step
recursion `walkMax (a :: l) = max 0 (a + walkMax l)`.
