# Laplace transform of the total branch length

Let `μ` be a probability measure and let `T_k` (`k ∈ ℕ`) be
[Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md) of a
sample of size `n` under `μ`: for `2 ≤ k ≤ n`, `T_k` has the exponential law with rate `C(k, 2)`,
and `T_2, …, T_n` are independent. Let `L = ∑_{k=2}^{n} k T_k` be the
[total branch length](../kingman-s-coalescent-and-watterson-s-estimator/total-length.md). Then
for every `u ≥ 0`,

`E[exp(-u L)] = ∏_{k=2}^{n} C(k, 2) / (C(k, 2) + k u) = ∏_{k=1}^{n-1} k / (k + 2u)`;

for `n ≤ 1` both sides are `1`.
