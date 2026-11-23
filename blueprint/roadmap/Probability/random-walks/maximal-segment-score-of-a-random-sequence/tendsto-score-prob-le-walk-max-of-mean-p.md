# With positive mean score the walk maximum diverges

Let `q` be a probability vector and `f` real scores on a finite alphabet with positive mean score,
`∑_b q_b f(b) > 0`. Then for every real `t`, `P(max_{k ≤ n} S_k ≥ t) → 1` as `n → ∞`, where
`max_{k ≤ n} S_k` is the [walk maximum](walk-max.md) of the scores of `n` independent letters with
law `q`. So, unlike under the negative-drift [Cramér–Lundberg bound](score-prob-le-walk-max-le.md),
the walk maximum, and by [Lindley duality](score-prob-le-lindley.md) the reflected walk, escapes to
infinity in probability.
