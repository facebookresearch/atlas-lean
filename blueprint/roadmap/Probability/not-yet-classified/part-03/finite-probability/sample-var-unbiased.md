# Sample Var Unbiased

The divide-by-`(n - 1)` sample variance `(∑ i, (x i - x̄) ^ 2) / (n - 1)`, meant for
`2 ≤ n` (MF06.3); it is unbiased for i.i.d. samples (`expectation_sampleVarUnbiased`). It is
ATLAS's finite-population variance `MathlibExt.Probability.Causality.popVar`, under the name
used here (`sampleVarUnbiased_eq_sum_div`). For `n ≤ 1` the value is a junk `0`: the sum is
empty for `n = 0`, and `n = 1` divides by `0`.
