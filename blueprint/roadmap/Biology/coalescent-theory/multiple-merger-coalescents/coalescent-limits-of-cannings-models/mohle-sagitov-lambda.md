# Möhle–Sagitov conditions for a Λ-coalescent limit

For a sequence of [Cannings models](../cannings-models/cannings-model.md), the `N`-th of
population size `N`, and a measure `Λ` on `[0, 1]`, the **Möhle–Sagitov conditions** are:

* the [coalescence probability](../cannings-models/coal-prob.md) `c_N` is positive for all large
  `N` and tends to `0`;
* for every `k ≥ 2`, the [probability](../cannings-models/merge-prob.md) `q_k` that `k` lineages
  merge in one generation satisfies `q_k / c_N → ∫ x^(k-2) Λ(dx)`;
* simultaneous mergers are negligible: `D_N / c_N → 0`, with `D_N` the
  [probability of a simultaneous double merger](../cannings-models/double-merge-prob.md).

Through the [factorial moments](merge-prob-mul-desc-factorial.md), with `ν_1` the
[number of offspring](../cannings-models/offspring.md) of a fixed parent and
`(x)_k = x (x - 1) ⋯ (x - k + 1)`, the second condition is the offspring condition
`E[(ν_1)_k] / (N^(k-1) c_N) → ∫ x^(k-2) Λ(dx)` of Möhle–Sagitov (2001), and the third is
equivalent to `E[(ν_1)_2 (ν_2)_2] / (N² c_N) → 0`, with `ν_2` the number of offspring of
another fixed parent. The limits `lim q_k / c_N`, for integers `k ≥ 2`, are the moments
`∫ x^(k-2) Λ(dx)` of `Λ`, so `Λ` is [determined by the model](eq-of-mohle-sagitov-lambda.md);
`k = 2` forces `Λ` to be a [probability measure](measure-real-univ-eq-one.md). For a measure of
infinite total mass `∫ 1 dΛ` takes the value `0` given to non-integrable functions, so the
conditions fail. The ratios are read as `0` at an `N` with `c_N = 0` (for instance `N ≤ 1`), by
the convention `x / 0 = 0`; the conditions concern only large `N`, where `c_N > 0`.
