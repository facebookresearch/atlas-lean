# Karlin–Altschul-type tail bound for the maximal segment score

Let `q` be a probability vector and `f` real scores on a finite alphabet, and let `θ ≥ 0` satisfy
`∑_b q_b e^{θ f(b)} = 1`. Then for every natural number `n` and every `t > 0`, the
[maximal segment score](max-seg-score.md) `Mₙ` of the scores of `n` independent letters with law
`q` satisfies `P(Mₙ ≥ t) ≤ n e^{-θ t}`, a union bound over the start of the best segment. For
`θ = 0`, which always satisfies the equation, the bound is `n`.
