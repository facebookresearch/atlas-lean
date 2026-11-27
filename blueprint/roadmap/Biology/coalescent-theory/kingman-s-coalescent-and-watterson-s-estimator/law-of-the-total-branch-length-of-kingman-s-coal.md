# Law of the total branch length of Kingman's coalescent

Let $n \ge 2$ and let $(T_k)_{2 \le k \le n}$ be a
[family of Kingman holding times](kingman-times.md), independent with
$T_k \sim \mathrm{Exp}\binom k2$, and let
[$L_n = \sum_{k=2}^n k\, T_k$](total-length.md) be the total branch length. Then
$k\, T_k \sim \mathrm{Exp}((k - 1)/2)$ and

$$\mathbb P(L_n \le x) = \bigl(1 - e^{-x/2}\bigr)^{n-1}, \qquad x \ge 0 ;$$

that is, $L_n / 2$ has the law of the maximum of $n - 1$ independent $\mathrm{Exp}(1)$ variables. For $n = 2$
this is $L_2 \sim \mathrm{Exp}(1/2)$, and the mean is $2 \sum_{j=1}^{n-1} 1/j$, as
[computed directly](integral-total-length.md).

## Depends on

- [Kingman holding times](kingman-times.md)
- [Total branch length](total-length.md)

## Proof depends on

- [Laplace transform of the total branch length](../infinite-sites-sampling-formula/integral-exp-neg-mul-total-length.md)

## Expansion

A sound expansion writes $L_n / 2 = \sum_{j=1}^{n-1} E_j / j$ with $E_j = j (j + 1) T_{j+1} / 2$ independent
$\mathrm{Exp}(1)$, and uses Rényi's representation of the maximum of $n - 1$ independent $\mathrm{Exp}(1)$
variables as such a sum of scaled spacings. Equivalently, for $u\ge0$ the Laplace transform
$\mathbb E\, e^{-u L_n} = \prod_{k=1}^{n-1} k/(k + 2u)$ equals
$\int_0^\infty e^{-ux}\, d\bigl(1 - e^{-x/2}\bigr)^{n-1} = (n - 1)\, B(2u + 1, n - 1)$, and Laplace transforms
determine laws on $[0, \infty)$.

## Sources

- S. Tavaré, "Line-of-descent and genealogical processes, and their applications in population genetics models", Theoretical Population Biology 26 (1984), 119–164, <https://doi.org/10.1016/0040-5809(84)90027-3>, Section 9.1, the integral form of equation (9.5), $\mathbb P(K_i = n) = \int_0^\infty e^{-\theta x} \frac{(\theta x)^n}{n!} (i - 1) e^{-x} (1 - e^{-x})^{i-2}\, dx$, whose mixing density $(i - 1) e^{-x}(1 - e^{-x})^{i - 2}$ is the density of half the total branch length of a sample of size $i$.
