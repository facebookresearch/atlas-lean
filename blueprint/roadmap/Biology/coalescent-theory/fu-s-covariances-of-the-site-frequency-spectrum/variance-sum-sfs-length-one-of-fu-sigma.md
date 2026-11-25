# Variance of $L_1 + \dots + L_{n-1}$ from Fu's closed form

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
`σ` for the sample size `n`, then

`Var(L_1 + ⋯ + L_{n-1}) = 4 a_2(n)`,

with [Tajima's constant](../segregating-sites-and-pairwise-differences/tajima-a2.md) `a_2(n) = ∑_{k=1}^{n-1} 1/k²`. Almost surely `L_1 + ⋯ + L_{n-1}` is the
total branch length `∑_{k=2}^{n} k T_k` ([total length over the frequency classes](../expected-site-frequency-spectrum/sum-sfs-length-ae-eq-total-length.md)), whose
variance is `4 a_2(n)` by Watterson (1975) ([variance of the total branch length](../segregating-sites-and-pairwise-differences/variance-total-length.md)).
For `n ≤ 1` the sum `L_1 + ⋯ + L_{n-1}` is empty, `a_2(n) = 0`, and both sides are `0`.
