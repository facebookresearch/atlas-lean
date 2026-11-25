# Fu's branch-length covariances from the topology identity

Let `μ` be a probability measure and let `T_k` (`k ∈ ℕ`) be
[Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md) of a
sample of size `n` under `μ`: for `2 ≤ k ≤ n`, `T_k` has the exponential law with rate `C(k, 2)`,
and `T_2, …, T_n` are independent. Let `τ` be a random block-size history such that every preimage
`τ⁻¹(A)` is measurable, with the
[random-joining law](../expected-site-frequency-spectrum/random-joining.md) from `n` singletons,
`μ(τ = ps) = R_{n-1}((1, …, 1), ps)` for every `ps`, and independent of the family `(T_k)_{k ∈ ℕ}`.
Let `L_i = ∑_{k=2}^{n} c_{k,i} T_k` be the
[total length of the branches subtending `i` sample copies](../expected-site-frequency-spectrum/sfs-length.md),
where `c_{k,i}` is the number of blocks of size `i` in entry `n - k` of `τ` (the empty list, which
contributes `0`, if `τ` has no such entry).

Suppose Fu's topology identity `F_n(i, j) = 4 σ_{ij}` holds for all `1 ≤ i, j ≤ n - 1`, where
`F_n` is the [moment sum](fu-topology-cov.md) and `σ_{ij}` is
[Fu's closed form](../fu-s-covariances-of-the-site-frequency-spectrum/fu-sigma.md). Then

`Cov(L_i, L_j) = 4 σ_{ij}` for all `1 ≤ i, j ≤ n - 1`.

This is the branch-length hypothesis under which
[Fu's covariance of the SFS](../fu-s-covariances-of-the-site-frequency-spectrum/covariance-count-kingman-of-fu-sigma.md)
is stated.
