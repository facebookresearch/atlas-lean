# Branch lengths sum almost surely to the total branch length

Let `T_k` be [Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md)
of a sample of size `n` under a measure `μ`: for `2 ≤ k ≤ n`, `T_k` has the exponential law with
rate `C(k, 2)`, and `T_2, …, T_n` are independent. Then `μ`-almost everywhere the
[branch lengths](kingman-branch-length.md) of the genealogy with epoch lengths
`E = (T_2, …, T_n)` sum to the
[total branch length](../kingman-s-coalescent-and-watterson-s-estimator/total-length.md):

`∑_b ℓ_b(E) = L = ∑_{k=2}^{n} k T_k`.

The equality can fail only where some `T_k` with `2 ≤ k ≤ n` is negative, a `μ`-null set.
