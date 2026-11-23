# The reflected walk and the walk maximum have equal tail weights

For real weights `q` and scores `f` on a finite alphabet, every natural number `n` and every real
`t`, the [score probability](score-prob.md) that the [Lindley reflected walk](lindley.md) after `n`
scores is at least `t` equals that of the [walk maximum](walk-max.md) being at least `t`:
`P(Wₙ ≥ t) = P(max_{k ≤ n} S_k ≥ t)`. For a probability vector `q` and a root `θ ≥ 0` of
`∑_b q_b e^{θ f(b)} = 1`, the [Cramér–Lundberg bound](score-prob-le-walk-max-le.md) then gives
`P(Wₙ ≥ t) ≤ e^{-θ t}` for every `n`.
