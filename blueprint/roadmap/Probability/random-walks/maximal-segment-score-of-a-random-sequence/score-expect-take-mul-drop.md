# Regeneration of the score sequence at a fixed time

For real weights `q` and scores `f` on a finite alphabet, natural numbers `k ≤ n` and real
functionals `F` and `G` of score lists, the [weighted average](score-expect.md) over words of length
`n` of `F(first k scores) · G(remaining n - k scores)` is `E_k[F] · E_{n-k}[G]`. For a probability
vector `q` the first `k` scores and the remaining `n - k` are independent.
