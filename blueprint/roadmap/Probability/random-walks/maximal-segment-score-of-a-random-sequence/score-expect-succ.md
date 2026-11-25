# First-step decomposition of the weighted average

For real weights `q` and scores `f` on a finite alphabet, every natural number `n` and every real
functional `F` of score lists, the [weighted average](score-expect.md) over words of length `n + 1`
decomposes over the first letter:
`E_{n+1}[F] = ∑_a q_a E_n[l ↦ F(f(a), l)]`, where `F(f(a), l)` is `F` of the list `f(a)` followed by
`l`.
