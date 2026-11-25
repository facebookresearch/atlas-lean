# Variance of a weighted sum of branch lengths from Fu's closed form

Let `μ` be a probability measure on a measurable space `Ω`, under which variances and covariances
are taken, and let `n` be a natural number. Let `T_k` (`k ∈ ℕ`) be
[Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md) of a sample of size `n` under `μ`: for `2 ≤ k ≤ n`, `T_k` has the
exponential law with rate `C(k, 2)`, and `T_2, …, T_n` are independent. Let `τ` be a random
block-size history (a random list of lists of block sizes) such that every preimage `τ⁻¹(A)` is
measurable, with the [random-joining law](../expected-site-frequency-spectrum/random-joining.md) from `n` singletons:
`μ(τ = ps) = R_{n-1}((1, …, 1), ps)` for every list `ps`, where `(1, …, 1)` has `n` entries
and `n - 1` is natural subtraction: for `n = 0` the initial list is empty, no step is taken,
and the law is concentrated on the history whose only entry is the empty list. Let
`L_i = ∑_{k=2}^{n} N_{k,i} T_k` be the [total length of the branches subtending `i` sample copies](../expected-site-frequency-spectrum/sfs-length.md),
where `N_{k,i}` is the number of blocks of size `i` in entry `n - k` of `τ` (`0` if there is no
such entry).

If `Cov(L_i, L_j) = 4 σ_{ij}` for all `1 ≤ i, j ≤ n - 1`, with [Fu's covariance matrix](fu-sigma.md)
`σ` for the sample size `n`, then for all real coefficients `c_i`

`Var(∑_{i=1}^{n-1} c_i L_i) = 4 ∑_{i=1}^{n-1} ∑_{j=1}^{n-1} c_i c_j σ_{ij}`.

For `n ≤ 1` these sums are empty and both sides are `0`.

The hypothesis on the covariances holds when, in addition, `τ` is independent of the family
`(T_k)_{k ∈ ℕ}` ([Fu's branch-length covariances](../fu-s-branch-length-covariances-for-every-sample/covariance-sfs-length-eq-four-mul-fu-sig.md)).
