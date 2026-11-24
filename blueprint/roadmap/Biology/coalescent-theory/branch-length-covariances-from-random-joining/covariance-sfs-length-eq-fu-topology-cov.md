# Branch-length covariances equal Fu's moment sum

Let `μ` be a probability measure and let `T_k` (`k ∈ ℕ`) be
[Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md) of a
sample of size `n` under `μ`: for `2 ≤ k ≤ n`, `T_k` has the exponential law with rate `C(k, 2)`,
and `T_2, …, T_n` are independent. Let `τ` be a random block-size history such that every preimage
`τ⁻¹(A)` is measurable, with the
[random-joining law](../expected-site-frequency-spectrum/random-joining.md) from `n` singletons,
`μ(τ = ps) = R_{n-1}((1, …, 1), ps)` for every `ps` (with `n - 1` truncated at `0`: for `n = 0`,
`R_0` starts from the empty list), and independent of the family `(T_k)_{k ∈ ℕ}`. Let
`L_i = ∑_{k=2}^{n} c_{k,i} T_k` be the
[total length of the branches subtending `i` sample copies](../expected-site-frequency-spectrum/sfs-length.md),
where `c_{k,i}` is the number of blocks of size `i` in entry `n - k` of `τ` (the empty list, which
contributes `0`, if `τ` has no such entry). Then for all natural numbers `i` and `j`,

`Cov(L_i, L_j) = F_n(i, j)`,

the deterministic [moment sum](fu-topology-cov.md)
`∑_{k=2}^{n} ∑_{l=2}^{n} E[c_{k,i} c_{l,j}] E[T_k T_l] - E[L_i] E[L_j]` of the block counts of
random joining and the Kingman holding times.
