# Defective renewal equation for the walk maximum

For real weights `q` and scores `f` on a finite alphabet, a level `t > 0` and a horizon `n`, the
[score probability](score-prob.md) that the [walk maximum](walk-max.md) of `n` scores is at least
`t` decomposes over the [first ladder epoch](is-first-ladder.md) `τ₊ = k` and the ladder height `H`:
`P_n(max_{j ≤ n} S_j ≥ t) = ∑_{k ≤ n} E_k[P_{n-k}(max ≥ t - H); τ₊ = k]`, where the summand is the
[weighted average](score-expect.md) over score lists of length `k` of the indicator that the list
ends at the first ladder epoch times the score probability that the walk maximum of `n - k` further
scores is at least `t - H`. For a probability vector `q` this is the finite-horizon defective
renewal equation: the tail of the maximum is determined by the joint law of the ladder epoch and
height.
