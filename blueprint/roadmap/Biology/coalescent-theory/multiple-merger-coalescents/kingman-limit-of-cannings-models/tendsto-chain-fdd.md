# Möhle–Sagitov: genealogies converge to Kingman's in finite dimensions

Let the sequence of [Cannings models](../cannings-models/cannings-model.md) `W_N` satisfy the
[Möhle–Sagitov conditions](mohle-sagitov.md) (`c_N > 0` for all large `N`, `c_N → 0` and
`μ_3 / (N² c_N) → 0`), with [pair-coalescence probabilities](pair-coalescence.md) `c_N` and third
[factorial moments](factorial-moment.md) `μ_3` of the offspring numbers, and let `n, k ∈ ℕ`, times
`0 ≤ t_0 ≤ t_1 ≤ ⋯ ≤ t_k` and
[partitions](../../partition-valued-kingman-coalescent/sample-partition.md) `x_0, …, x_k` of the
sample `{0, …, n - 1}`. As `N → ∞`, the [finite-dimensional distribution](chain-fdd.md) of the
ancestral partition process of the sample under `W_N`, with transition matrix the
[ancestral matrix](ancestral-matrix.md) `Π_N`, started from the partition `⊥` into singletons at
generation `0` and observed at the generations `m_i = ⌊t_i / c_N⌋`, converges to the
[finite-dimensional distribution of Kingman's `n`-coalescent](kingman-fdd.md) started from
singletons, at the times `t_i`. That is,

`Π_N^(m_0)(⊥, x_0) ∏_{i < k} Π_N^(m_{i+1} - m_i)(x_i, x_{i+1})`

converges to

`exp(t_0 Q_n)(⊥, x_0) ∏_{i < k} exp((t_{i+1} - t_i) Q_n)(x_i, x_{i+1})`.

Here `⌊y⌋` is the largest natural number at most `y`, `exp` is the matrix exponential and `Q_n` is
the [rate matrix](../../partition-valued-kingman-coalescent/partition-rate.md) of Kingman's
partition-valued coalescent (Möhle 2000; Möhle–Sagitov 2001). At an `N` with `c_N = 0` (for instance
`N ≤ 1`), every `t_i / c_N = 0`, so every `m_i = 0` and every factor on the left is an entry of the
identity matrix; this does not affect the limit.
