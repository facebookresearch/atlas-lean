# Steel's conjecture, CFN case

**Steel's conjecture, CFN case** (Daskalakis-Mossel-Roch 2011, Theorem 1):
hypotheses are leaf count (`hn`), a binary tree on `n` leaves (`T`,
`hleaves`), edge lengths that are `Δ`-multiples in `[f, g]` with
`g < ln 2 / 4` (`hlen`, `hg`, `hpos`), CFN flips in range (`hflip`), a
sample size `k = c * (log n + log 1/δ)` (`hk`, `hdelta`), character data
(`samples`: `k` binary characters on the leaves), and reconstruction
(`rec`: topology recovered; `hsucc`: success probability at least
`1 - δ`). Conclusion: the success probability bound holds, i.e. topology
reconstruction from `O(log n)` characters below threshold.

## Sources

- Daskalakis-Mossel-Roch (2011), Theorem 1.
