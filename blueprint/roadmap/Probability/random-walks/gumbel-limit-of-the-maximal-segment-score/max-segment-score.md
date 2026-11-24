# Maximal segment score of the first n scores

For a sequence of real scores `x 0, x 1, …` and a natural number `n`, the maximal segment score is
`Mₙ = max_{0 ≤ i ≤ j ≤ n} (x i + ⋯ + x (j - 1))`, the largest [segment score](segment-score.md) of a
segment of the first `n` scores `x 0, …, x (n - 1)`. The empty segment is allowed, so `Mₙ ≥ 0` and
`M₀ = 0`.
