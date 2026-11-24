# Finite-dimensional distributions of Kingman's coalescent

For `n, k ∈ ℕ`, real times `t_0, …, t_k` and
[partitions](../../partition-valued-kingman-coalescent/sample-partition.md) `x_0, …, x_k` of the
sample `{0, …, n - 1}`, the value is

`exp(t_0 Q_n)(⊥, x_0) ∏_{i < k} exp((t_{i+1} - t_i) Q_n)(x_i, x_{i+1})`,

where `exp` is the matrix exponential, `Q_n` is the
[rate matrix](../../partition-valued-kingman-coalescent/partition-rate.md) of Kingman's
partition-valued coalescent, `⊥` is the partition into singletons and `exp(t_0 Q_n)(⊥, x_0)` is the
[time-`t_0` marginal](../../partition-valued-kingman-coalescent/time-law.md). The formula is defined
for all real times. For `0 ≤ t_0 ≤ t_1 ≤ ⋯ ≤ t_k` it is the finite-dimensional distribution of
Kingman's `n`-coalescent: the probability that the coalescent, started from singletons at time `0`,
is at `x_i` at time `t_i` for every `i`.
