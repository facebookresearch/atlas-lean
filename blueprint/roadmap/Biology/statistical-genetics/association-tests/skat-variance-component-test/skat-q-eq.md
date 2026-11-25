# The SKAT statistic as a quadratic form in P y

For every real `n × q` covariate matrix `X`, real `n × n` matrix `V`, real `n × m` genotype matrix
`G`, real weights `w` and phenotype `y ∈ ℝⁿ`, the [SKAT statistic](skat-q.md) is

`Q = (P y)ᵀ K (P y)`,

with `P` the [null projection](proj-p.md) and `K` the [SKAT kernel](skat-kernel.md). Equivalently,
`Q` is the [kernel score statistic](../../../../Probability/hypothesis-testing/score-wald-and-likelihood-ratio-tests/kernel-q.md) `Q_K(y) = (P y)ᵀ K (P y)`
of the SKAT kernel `K = G diag(w) Gᵀ`: `Q(y) = Q_K(y)` for every `y`.
