# Under Möhle–Sagitov, rescaled transitions converge to Kingman's rates

Let the sequence of [Cannings models](../cannings-models/cannings-model.md) `W_N` satisfy the
[Möhle–Sagitov conditions](mohle-sagitov.md) (`c_N > 0` for all large `N`, `c_N → 0` and
`μ_3 / (N² c_N) → 0`), with [pair-coalescence probabilities](pair-coalescence.md) `c_N` and third
[factorial moments](factorial-moment.md) `μ_3` of the offspring numbers, and let `n ∈ ℕ`. Then,
entrywise as `N → ∞`,

`c_N⁻¹ (Π_N - I) → Q_n`,

where `Π_N` is the [ancestral matrix](ancestral-matrix.md) of a sample of `n` genes under `W_N`, `I`
is the identity matrix and `Q_n` is the
[rate matrix](../../partition-valued-kingman-coalescent/partition-rate.md) of Kingman's
partition-valued coalescent: each pair of blocks merges at rate `1`, a partition with `k` blocks is
left at total rate `k (k - 1) / 2`, and every other change of partition has rate `0`. Where
`c_N = 0` (for instance `N ≤ 1`), `c_N⁻¹ (Π_N - I)` is the zero matrix (`0⁻¹ = 0`); this does not
affect the limit.
