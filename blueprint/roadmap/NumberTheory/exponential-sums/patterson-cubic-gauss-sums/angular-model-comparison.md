# Cubic Gauss sums compared with the angular model

For each fixed $\ell\in\mathbb Z$, as the real cutoff $X\to+\infty$,

$$
\sum_{\substack{p\ \mathrm{primary\ prime}\\ N(p)\le X}}
 \theta_\ell(p)\bigl(G(p)-c_*N(p)^{-1/6}\bigr)
 =o\!\left(\frac{X^{5/6}}{\log X}\right).
$$

The assertion includes $\ell=0$ and does not assert uniformity in $\ell$.

## Depends on

- [Normalized cubic Gauss sum and angular mode](normalized-cubic-gauss-sum.md)

## Expansion

Separate the cubic theta comparison from the prime cutoff argument. Establish the smoothed-to-sharp error bound in each fixed angular mode for the specified residue normalization.

## Sources

- [PattersonFirstMoment.lean — `patterson_angularComparison`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PattersonFirstMoment.lean#L87-L90)
