# Fu's branch-length covariances under Kingman's coalescent

Let `μ` be a probability measure on a measurable space `Ω` and `n` a natural number. Let `(T_k)`
be [Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md) of a sample of size `n` under `μ`: for
`2 ≤ k ≤ n`, `T_k` is exponential with rate `C(k, 2)`, and `T_2, …, T_n` are mutually independent.
Let `τ` be a random list of block-size lists such that every preimage `τ⁻¹(S)` is measurable, with
the [random-joining law](../expected-site-frequency-spectrum/random-joining.md) from `n` singletons,
`μ(τ = p) = R_{n-1}((1, …, 1), p)` for every `p`, and such that `τ` and the family `(T_k)_{k ∈ ℕ}`
are independent under `μ`. Let
`L_i = ∑_{k=2}^{n} c_i(τ_{n-k}) T_k` be the
[total length of the branches subtending exactly `i` sample copies](../expected-site-frequency-spectrum/sfs-length.md), where
`c_i(τ_{n-k})` is the number of entries equal to `i` in the entry of index `n - k` of `τ` (the
block sizes while `k` lineages remain; the empty list if there is no such entry).
Then for all `i`, `j` with `1 ≤ i, j ≤ n - 1`,

`Cov(L_i, L_j) = 4 σ_{ij}`,

where `σ_{ij}` is [Fu's closed form](../fu-s-covariances-of-the-site-frequency-spectrum/fu-sigma.md). So the branch-length hypothesis of
[Fu's covariance of the SFS from the closed form](../fu-s-covariances-of-the-site-frequency-spectrum/covariance-count-kingman-of-fu-sigma.md)
holds.
