# Under Möhle–Sagitov, transition matrices converge to Kingman's

Let the sequence of [Cannings models](../cannings-models/cannings-model.md) `W_N` satisfy the
[Möhle–Sagitov conditions](mohle-sagitov.md), with
[pair-coalescence probabilities](pair-coalescence.md) `c_N`, and let `n ∈ ℕ` and `0 ≤ s ≤ t`. Then,
entrywise as `N → ∞`,

`Π_N ^ (⌊t / c_N⌋ - ⌊s / c_N⌋) → exp((t - s) Q_n)`,

where `Π_N` is the [ancestral matrix](ancestral-matrix.md) of a sample of `n` genes under `W_N`,
`⌊y⌋` is the largest natural number at most `y`, `exp` is the matrix exponential and `Q_n` is the
[rate matrix](../../partition-valued-kingman-coalescent/partition-rate.md) of Kingman's
partition-valued coalescent. The left side is the transition matrix of the ancestral partition from
generation `⌊s / c_N⌋` to generation `⌊t / c_N⌋`, the right side that of Kingman's `n`-coalescent
over a time `t - s` (Möhle 2000; Möhle–Sagitov 2001).
