# Maximal segment score of a score list

For a list of real scores `x₀, …, x_{n-1}` with partial sums `S_k = x₀ + ⋯ + x_{k-1}`, the maximal
segment score is `Mₙ = max_{0 ≤ i ≤ j ≤ n} (S_j - S_i)`, the largest sum of a possibly empty
contiguous run ([upper bound](sum-le-max-seg-score-of-infix.md),
[attained](exists-infix-sum-eq-max-seg-score.md)); it is `0` for the empty list and at least `0` in
general. It is computed by one left-to-right pass carrying the current value of the
[reflected walk](lindley.md) and the best value so far: one addition and at most two comparisons
per score.
