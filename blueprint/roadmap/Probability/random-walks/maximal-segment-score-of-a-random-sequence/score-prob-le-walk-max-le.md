# Finite-horizon Cramér–Lundberg bound for the walk maximum

Let `q` be a probability vector and `f` real scores on a finite alphabet, and let `θ ≥ 0` satisfy
`∑_b q_b e^{θ f(b)} = 1`. Then for every horizon `n` and every real `t`, the
[walk maximum](walk-max.md) of the scores of `n` independent letters with law `q` satisfies
`P(max_{k ≤ n} S_k ≥ t) ≤ e^{-θ t}`. For `θ = 0`, which always satisfies the equation, the bound
is `1` and says nothing; it is informative for a root `θ > 0`.
