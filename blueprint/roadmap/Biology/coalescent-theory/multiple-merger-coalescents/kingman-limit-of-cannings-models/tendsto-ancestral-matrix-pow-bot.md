# Möhle–Sagitov: from singletons, the law at time t tends to Kingman's

Let the sequence of [Cannings models](../cannings-models/cannings-model.md) `W_N` satisfy the
[Möhle–Sagitov conditions](mohle-sagitov.md) (`c_N > 0` for all large `N`, `c_N → 0` and
`μ_3 / (N² c_N) → 0`), with [pair-coalescence probabilities](pair-coalescence.md) `c_N` and third
[factorial moments](factorial-moment.md) `μ_3` of the offspring numbers, and let `n ∈ ℕ`, `t ≥ 0`
and `π` be a [partition](../../partition-valued-kingman-coalescent/sample-partition.md) of the
sample `{0, …, n - 1}`. Then, as `N → ∞`,

`Π_N ^ ⌊t / c_N⌋ (⊥, π) → exp(t Q_n)(⊥, π)`,

where `Π_N` is the [ancestral matrix](ancestral-matrix.md) of the sample under `W_N`, `⊥` is the
partition into singletons, `⌊y⌋` is the largest natural number at most `y` and `exp(t Q_n)` is the
matrix exponential of `t` times the
[rate matrix](../../partition-valued-kingman-coalescent/partition-rate.md) `Q_n` of Kingman's
partition-valued coalescent. The left side is the probability that the ancestral partition, started
from singletons, is `π` after `⌊t / c_N⌋` generations; the right side is the
[time-t marginal](../../partition-valued-kingman-coalescent/time-law.md) of Kingman's `n`-coalescent
started from singletons. At an `N` with `c_N = 0` (for instance `N ≤ 1`), `t / c_N = 0`, so
`⌊t / c_N⌋ = 0` and the matrix power is the identity; this does not affect the limit.
