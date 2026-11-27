# A possible positive score makes the maximal segment score unbounded

Let `q` be a probability vector and `f` real scores on a finite alphabet, with some letter `b₀` of
positive probability `q_{b₀} > 0` and positive score `f(b₀) > 0`. Then for every real `t`,
`P(Mₙ ≥ t) → 1` as `n → ∞`, where `Mₙ` is the [maximal segment score](max-seg-score.md) of the
scores of `n` independent letters with law `q`. Under negative drift the walk maximum itself stays
tight ([Cramér–Lundberg bound](score-prob-le-walk-max-le.md)); the growth rate
`Mₙ / log n → 1 / θ` is a further result (Karlin and Dembo 1992).
