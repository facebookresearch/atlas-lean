# Without positive scores, a positive segment score has weight zero

Let `q` be nonnegative weights and `f` real scores on a finite alphabet with `f(b) ≤ 0` for every
letter `b` of positive weight `q_b > 0`. Then for every natural number `n`, the
[score probability](score-prob.md) that the [maximal segment score](max-seg-score.md) of `n` scores
is positive is `0`. When `q` is a probability vector, `P(X > 0) = 0` and `Mₙ = 0` almost surely.
