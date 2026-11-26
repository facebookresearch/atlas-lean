# Expected precision is the average marginal relevance

For arbitrary real weights `μ` on the relevance vectors `Fin N → Bool`, a ranked
prefix `r : Fin k → Fin N` and `k ≠ 0`, the `μ`-weighted precision at `k` (the sum over
relevance vectors of their weight times their precision at `k`) equals the sum of the
marginal relevances of the documents `r j`, divided by `k`. When `μ` is nonnegative with
total weight `1`, a joint relevance law, this says that expected precision is the average
marginal relevance; no independence between documents is assumed.
