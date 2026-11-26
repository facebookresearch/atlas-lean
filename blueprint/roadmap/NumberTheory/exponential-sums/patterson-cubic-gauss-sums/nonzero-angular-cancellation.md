# Cancellation in each nonzero angular mode of the cubic first moment

For every fixed nonzero integer $\ell$,

$$
\sum_{\substack{p\ \mathrm{primary\ prime}\\ N(p)\le X}}\theta_\ell(p)G(p)
 =o\!\left(\frac{X^{5/6}}{\log X}\right)\qquad(X\to+\infty).
$$

Both signs of the mode are included. This is a sharp real-norm cutoff and is not a uniform estimate
as $|\ell|\to\infty$.

## Depends on

- [Normalized cubic Gauss sum and angular mode](normalized-cubic-gauss-sum.md)

## Proof depends on

- [Angular model comparison](angular-model-comparison.md)

## Expansion

Construct the primitive angular Hecke character in each nonzero mode, account for the primary convention and show its prime sum has no main term. Partial summation gives the required bound for the weighted angular model to combine with the comparison.

## Sources

- [PattersonFirstMoment.lean — `patterson_angularCancellation`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PattersonFirstMoment.lean#L91-L94)
