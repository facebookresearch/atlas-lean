# Tajima's b₁ from the squared weights of θ_π

For every natural number `n ≥ 2`,

`∑_{i=1}^{n-1} ((n - i) / C(n, 2))² i = b_1 = (n + 1) / (3 (n - 1))`,

[Tajima's constant b₁](../segregating-sites-and-pairwise-differences/tajima-b1.md) (Tajima 1983).
The left side is `∑_i a_i² / i` for the coefficients `a_i = i (n - i) / C(n, 2)` of `θ_π` on the
site frequency spectrum, so `b_1 θ` is the first-order term of the
[variance of θ_π under Kingman's coalescent](variance-theta-pi-kingman.md).
