# Variance of the branch-length $\theta_\pi$ from Fu's closed form

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
`σ` for the sample size `n`, then [Tajima's estimator](../site-frequency-spectrum-under-variable-populatio/theta-pi.md) `θ_π` evaluated on the branch
lengths satisfies

`Var(∑_{i=1}^{n-1} π_i L_i) = 4 b_2(n)`, with `π_i = i (n - i) / C(n, 2)`

and [Tajima's constant](../segregating-sites-and-pairwise-differences/tajima-b2.md) `b_2(n) = 2 (n² + n + 3) / (9 n (n - 1))` (Tajima 1983).
