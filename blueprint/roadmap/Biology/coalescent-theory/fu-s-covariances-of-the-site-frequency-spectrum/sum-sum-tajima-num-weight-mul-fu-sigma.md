# Tajima's $c_2$ from Fu's closed form

For a natural number `n ≥ 2`, let `w_i = i (n - i) / C(n, 2) - 1 / a_1(n)`, the
[weights of Tajima's `D` numerator](../covariances-of-the-site-frequency-spectrum/tajima-num-weight.md), where `a_1(n) = ∑_{k=1}^{n-1} 1/k`: for
`θ_π = ∑_{i=1}^{n-1} i (n - i) ξ_i / C(n, 2)` and `S = ∑_{i=1}^{n-1} ξ_i`,
`θ_π - S / a_1(n) = ∑_{i=1}^{n-1} w_i ξ_i`. With [Fu's covariance matrix](fu-sigma.md) `σ` for the
sample size `n`,

`∑_{i=1}^{n-1} ∑_{j=1}^{n-1} w_i w_j σ_{ij} = c_2(n)`,

[Tajima's constant](../segregating-sites-and-pairwise-differences/tajima-c2.md) `c_2(n) = b_2(n) - (n + 2) / (a_1(n) n) + a_2(n) / a_1(n)²` (Tajima 1989), with
`a_2(n) = ∑_{k=1}^{n-1} 1/k²` and `b_2(n) = 2 (n² + n + 3) / (9 n (n - 1))`. It follows from
`∑_{i,j} π_i π_j σ_{ij} = b_2(n)`, `∑_{i,j} π_i σ_{ij} = (n + 2) / (2n)` and
`∑_{i,j} σ_{ij} = a_2(n)`, with `π_i = i (n - i) / C(n, 2)` and sums over `1 ≤ i, j ≤ n - 1`.
