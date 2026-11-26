# Variance of the branch-length $D$ numerator from Fu's closed form

Let `μ` be a probability measure on a measurable space `Ω`, under which variances and covariances
are taken, and let `n ≥ 2` be a natural number. Let `T_k` (`k ∈ ℕ`) be
[Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md) of a sample of size `n` under `μ`: for `2 ≤ k ≤ n`, `T_k` has the
exponential law with rate `C(k, 2)`, and `T_2, …, T_n` are independent. Let `τ` be a random
block-size history (a random list of lists of block sizes) such that every preimage `τ⁻¹(A)` is
measurable, with the [random-joining law](../expected-site-frequency-spectrum/random-joining.md) from `n` singletons:
`μ(τ = ps) = R_{n-1}((1, …, 1), ps)` for every list `ps`, where `(1, …, 1)` has `n` entries. Let
`L_i = ∑_{k=2}^{n} N_{k,i} T_k` be the [total length of the branches subtending `i` sample copies](../expected-site-frequency-spectrum/sfs-length.md),
where `N_{k,i}` is the number of blocks of size `i` in entry `n - k` of `τ` (`0` if there is no
such entry).

If `Cov(L_i, L_j) = 4 σ_{ij}` for all `1 ≤ i, j ≤ n - 1`, with [Fu's covariance matrix](fu-sigma.md)
`σ` for the sample size `n`, then the [weights of Tajima's `D` numerator](../covariances-of-the-site-frequency-spectrum/tajima-num-weight.md)
`w_i = i (n - i) / C(n, 2) - 1 / a_1(n)`, applied to the branch lengths, give

`Var(∑_{i=1}^{n-1} w_i L_i) = 4 c_2(n)`,

with [Tajima's constant](../segregating-sites-and-pairwise-differences/tajima-c2.md) `c_2(n) = b_2(n) - (n + 2) / (a_1(n) n) + a_2(n) / a_1(n)²`
(Tajima 1989), where `a_1(n) = ∑_{k=1}^{n-1} 1/k`, `a_2(n) = ∑_{k=1}^{n-1} 1/k²` and
`b_2(n) = 2 (n² + n + 3) / (9 n (n - 1))`.
