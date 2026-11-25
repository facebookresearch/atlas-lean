# Unit-hydrograph outflow as a discrete convolution

For a rainfall-excess sequence `p` and a unit-hydrograph response `u` on the time steps
`0, 1, 2, …` (any real sequences, not necessarily nonnegative), the outflow at step `k` is the
discrete convolution `q k = ∑_{i + j = k} p i * u j`, the sum over the pairs of natural numbers
`(i, j)` with `i + j = k`: the [sum convolution](../../../../Combinatorics/additive-combinatorics/additive-bases/additive-representation-functions/sum-conv.md) of `p` and `u`. Steps are counted from `0`,
where the engineering sources count from `1` (`p i = P (i + 1)`, `u j = U (j + 1)`,
`q k = Q (k + 1)`).
