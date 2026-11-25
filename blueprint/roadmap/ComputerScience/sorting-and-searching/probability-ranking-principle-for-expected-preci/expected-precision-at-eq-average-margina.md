# Expected precision is the average marginal relevance

For a joint relevance law `μ` on `Fin N → Bool`, a ranked prefix `r : Fin k →
Fin N` and `k ≠ 0`, the expected precision at `k` equals the sum of the
marginal relevances of the documents `r j`, divided by `k`. This is linearity
of expectation for a finite joint law; no independence between documents is
assumed.
