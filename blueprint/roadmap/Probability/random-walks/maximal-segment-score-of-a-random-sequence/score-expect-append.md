# The weighted average factors over two consecutive blocks

For real weights `q` and scores `f` on a finite alphabet, natural numbers `k` and `m` and every
real functional `F` of score lists, the [weighted average](score-expect.md) over words of length
`k + m` is the iterated average over a word `u` of length `k` and a word `v` of length `m`:
`E_{k+m}[F] = E_k[u ↦ E_m[v ↦ F(u v)]]`. For a probability vector `q` this says that a word of
length `k + m` is a word of length `k` followed by an independent word of length `m`.
