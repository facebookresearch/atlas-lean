# Maximum of the score walk

For a list of real scores `x₀, …, x_{n-1}`, with partial sums `S_k = x₀ + ⋯ + x_{k-1}` and `S₀ = 0`,
the walk maximum is `max_{0 ≤ k ≤ n} S_k`, the largest sum of a possibly empty prefix
([upper bound](sum-le-walk-max-of-prefix.md), [attained](exists-prefix-sum-eq-walk-max.md)). It is
`0` for the empty list and is computed by the first-step recursion: the walk maximum of
`a, x₁, …, x_{n-1}` is `max(0, a + w)`, where `w` is the walk maximum of `x₁, …, x_{n-1}`; in
particular it is at least `0`.
