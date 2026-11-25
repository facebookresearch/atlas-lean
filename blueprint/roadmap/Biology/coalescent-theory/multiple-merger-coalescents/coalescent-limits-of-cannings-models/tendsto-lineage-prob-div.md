# Under Möhle–Sagitov, rescaled transitions converge to the jump rates

Under the [Möhle–Sagitov conditions](mohle-sagitov-lambda.md) (`c_N > 0` for all large `N`,
`c_N → 0`, `q_k / c_N → ∫ x^(k-2) Λ(dx)` for every `k ≥ 2`, and `D_N / c_N → 0`, with `q_k` the
probability that `k` sampled lineages share a parent and `D_N` that of a simultaneous double merger)
for a sequence of Cannings models and a finite measure `Λ` on `[0, 1]`, for all `a < b` the
[probability](../cannings-models/lineage-prob.md) `P^{(N)}_{b,a}` that `b` lineages have `a` parents
satisfies `P^{(N)}_{b,a} / c_N → C(b, k) λ_{b,k}` as `N → ∞`, with `c_N` the
[coalescence probability](../cannings-models/coal-prob.md) of the `N`-th model, `k = b + 1 - a` and
`λ_{b,k}` the [merger rate](../../coalescents/merger-rate.md) of the Λ-coalescent: the jump rate
from `b` to `a` blocks. At an `N` with `c_N = 0` (for instance `N ≤ 1`) the ratio is `0`, by the
convention `x / 0 = 0`; this does not affect the limit.
