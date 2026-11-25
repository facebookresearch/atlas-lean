# Factorial moments of the number of exceeding diagonals

For real weights `p` and `q` on a finite alphabet, a real score `s` on pairs of letters, natural
numbers `m` and `n`, a real `t` and a natural number `k`, the `k`-th exceedance moment `S_k` is
the [two-sequence average](two-expect.md) of `C(W, k)` over words `u` and `v` of lengths `m` and
`n`, where `W` is the [number of diagonals exceeding](exceed-count.md) `t`. It equals the sum,
over the sets `T` of `k` [offsets](offsets.md), of the [two-sequence probability](two-prob.md)
that every diagonal in `T` has maximal segment score greater than `t`. When `p` and `q` are
probability vectors, `S_k = E[C(W, k)]` is the `k`-th factorial (binomial) moment of `W`, and
`S_0 = 1`.
