# Splitting a score sequence at a fixed position

For real weights `q` and scores `f` on a finite alphabet, natural numbers `k ≤ n` and every real
functional `Φ` of two score lists, the [weighted average](score-expect.md) over words of length `n`
of `Φ` of the first `k` scores and the remaining `n - k` scores is the iterated average
`E_k[u ↦ E_{n-k}[v ↦ Φ(u, v)]]`. For a probability vector `q` the two blocks are independent.
