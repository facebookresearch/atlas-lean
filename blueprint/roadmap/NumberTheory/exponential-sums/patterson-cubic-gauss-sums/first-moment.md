# The sharp first moment for cubic Gauss sums

As real $X\to+\infty$ the all-primary-prime sum satisfies

$$
\sum_{\substack{p\ \mathrm{primary\ prime}\\ N(p)\le X}}G(p)
 =\frac65 c_*\frac{X^{5/6}}{\log X} + o\!\left(\frac{X^{5/6}}{\log X}\right).
$$

The main term is real and positive for large $X$; the error is complex. No conjectural premise is
assumed, and both primary conjugates are included when they are distinct.

## Depends on

- [Normalized cubic Gauss sum](normalized-cubic-gauss-sum.md)

## Proof depends on

- [Angular model comparison at mode zero](angular-model-comparison.md)

## Expansion

Add the prime-number theorem for primary Eisenstein primes with this element count. Partial summation of $N(p)^{-1/6}$ should give the factor $6/5$. Combine with the zero-mode comparison.

## Sources

- [PattersonFirstMoment.lean — `patterson_firstMoment`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PattersonFirstMoment.lean#L83-L86)
