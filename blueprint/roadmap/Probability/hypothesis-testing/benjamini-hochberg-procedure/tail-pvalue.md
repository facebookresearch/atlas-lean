# P-values of a family of gene-level tests

For `m` gene-level tests with statistics `T i : Ω → ℝ` and reference upper tails `G i : ℝ → ℝ`,
`i = 0, …, m - 1`, the p-value of test `i` at the outcome `ω` is `p_i(ω) = G i (T i ω)`, its
reference tail evaluated at its statistic. Any real functions are allowed;
[tail-calibrated families](is-tail-calibrated-family.md) add the conditions under which these
p-values are measurable and, for the null genes, valid.
