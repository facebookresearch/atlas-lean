# Fu's branch-length covariances for samples of size at most four

Let `n ≤ 4`, let `μ` be a probability measure and let `T_k` (`k ∈ ℕ`) be
[Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md) of a
sample of size `n` under `μ`: for `2 ≤ k ≤ n`, `T_k` has the exponential law with rate `C(k, 2)`,
and `T_2, …, T_n` are independent. Let `τ` be a random block-size history such that every preimage
`τ⁻¹(A)` is measurable, with the
[random-joining law](../expected-site-frequency-spectrum/random-joining.md) from `n` singletons,
`μ(τ = ps) = R_{n-1}((1, …, 1), ps)` for every `ps`, and independent of the family `(T_k)_{k ∈ ℕ}`.
Let `L_i = ∑_{k=2}^{n} c_{k,i} T_k` be the
[total length of the branches subtending `i` sample copies](../expected-site-frequency-spectrum/sfs-length.md),
where `c_{k,i}` is the number of blocks of size `i` in entry `n - k` of `τ` (the empty list, which
contributes `0`, if `τ` has no such entry). Then

`Cov(L_i, L_j) = 4 σ_{ij}` for all `1 ≤ i, j ≤ n - 1`,

with [Fu's closed form](../fu-s-covariances-of-the-site-frequency-spectrum/fu-sigma.md)
`σ_{ij}`, with no further hypothesis: the
[topology identity](fu-topology-cov-eq-four-mul-fu-sigma-of.md) holds for these sample sizes. It
is the case `n ≤ 4` of the
[result for every sample size](../fu-s-branch-length-covariances-for-every-sample/covariance-sfs-length-eq-four-mul-fu-sig.md).
