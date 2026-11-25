# Weights of Tajima's D numerator on the site frequency spectrum

For natural numbers `n` and `i`, let

`w_{n,i} = i (n - i) / C(n, 2) - 1 / a_1`,

where `a_1 = ∑_{k=1}^{n-1} 1 / k` is
[Tajima's constant a₁](../segregating-sites-and-pairwise-differences/tajima-a1.md) and `n - i` is
a difference of real numbers. For `n ≥ 2` and `1 ≤ i ≤ n - 1` it is the coefficient of `ξ_i` in
Tajima's `D` numerator `θ_π - S / a_1` written on the site frequency spectrum, where
`θ_π = ∑_{i=1}^{n-1} i (n - i) ξ_i / C(n, 2)` and `S = ∑_{i=1}^{n-1} ξ_i`. With the conventions
`x / 0 = 0` and `0⁻¹ = 0` it is defined for every `n`: for `n ≤ 1`, where `C(n, 2) = 0` and
`a_1 = 0`, it is `0`.
