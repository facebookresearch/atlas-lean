# One generation of the neutral Wright–Fisher chain

One generation of the neutral Wright–Fisher chain with `M` gene copies, acting on continuous
functions of the allele frequency: `(wfStep M f)(x) = ∑_k f(k/M) C(M, k) x^k (1 - x)^(M - k)`,
which for `M ≥ 1` is the expected value of `f` at the next frequency `Bin(M, x) / M` (the `M`-th
Bernstein operator, Mathlib's `bernsteinApproximation`; the expectation is
`ProbabilityTheory.integral_binomial`). It is a linear
contraction. At `M = 0` it returns the constant `f 0` (Lean's `k / 0 = 0`; no population).
