# Calibration of the exact allelic test at attainable levels

Let `n₁` and `n₂` be natural numbers, `0 < f < 1`, and `X, Y : Ω → ℕ` measurable allele counts that
are independent under a measure `μ`, with laws `Bin(n₁, f)` and `Bin(n₂, f)` under `μ` (so `μ` is a
probability measure). Let `t ≤ n₁ + n₂` and let `H = H(n₁ + n₂, n₁, t)` be the
[hypergeometric law](../../distributions/discrete/hypergeometric-distribution/hypergeometric.md).
Then for every natural number `k`, with `s_k = H{j ≥ k}` the
[upper tail](../valid-p-values-and-false-discovery-proportion/upper-tail.md)
of `H` at `k`, the [allelic p-value](allelic-pvalue.md) `p` satisfies
`μ(p ≤ s_k | X + Y = t) = s_k`. Here `μ(A | B) = μ(A ∩ B) / μ(B)` is the conditional probability
given the margin, whose event has positive probability under these hypotheses. So, given the
margin, the p-value is exactly calibrated at each attainable level `s_k`.
