# Expected Precision At

Expected precision at cutoff `k` under a finite joint relevance law `μ`.

For a relevance vector `rel`, the relevance predicate is `fun i => rel i = true`.
When `μ` is nonnegative with total weight `1`, this is the expectation of
`precisionAt` under `μ`; the identity below is just finite linearity and uses
no independence.
