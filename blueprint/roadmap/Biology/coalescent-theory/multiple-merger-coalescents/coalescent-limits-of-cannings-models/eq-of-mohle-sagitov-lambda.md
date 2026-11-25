# The limit Λ is determined by the offspring law

For a sequence of Cannings models and two finite measures `Λ` and `Λ'` on `[0, 1]` that both satisfy
the [Möhle–Sagitov conditions](mohle-sagitov-lambda.md) for this same sequence, `Λ = Λ'`. The
condition used is `q_k / c_N → ∫ x^(k-2) Λ(dx)` for every `k ≥ 2`, with `q_k` the probability that
`k` sampled lineages share a parent and `c_N` the coalescence probability: the moments of `Λ` and
`Λ'` are the same limits, and a finite measure is
[determined by its merger rates](../../coalescents/eq-of-merger-rate-eq.md) (Pitman's uniqueness
theorem). At an `N` with `c_N = 0` (for instance `N ≤ 1`) the ratio `q_k / c_N` is `0`, by the
convention `x / 0 = 0`; the limits depend only on large `N`, where `c_N > 0`.
