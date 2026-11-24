# Tajima's c₁ from the squared weights of the D numerator

For every natural number `n ≥ 2`,

`∑_{i=1}^{n-1} w_{n,i}² / i = c_1 = b_1 - 1 / a_1`,

where `w_{n,i} = i (n - i) / C(n, 2) - 1 / a_1` are the
[weights of Tajima's D numerator](tajima-num-weight.md), `a_1 = ∑_{k=1}^{n-1} 1 / k`,
`b_1 = (n + 1) / (3 (n - 1))`, and `c_1` is
[Tajima's constant c₁](../segregating-sites-and-pairwise-differences/tajima-c1.md) (Tajima 1989).
So `c_1 θ` is the first-order term of the
[variance of Tajima's D numerator under Kingman's coalescent](variance-tajima-numerator-kingman.md).
