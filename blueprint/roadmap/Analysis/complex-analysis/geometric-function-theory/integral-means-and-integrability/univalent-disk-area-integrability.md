# Area integrability of derivative moments of univalent disk maps

If $f$ is holomorphic and injective on the open unit disk, then $z\mapsto|f'(z)|^t$ is Lebesgue-area integrable on the disk for every real $-2<t<2/3$. The map need not have bounded image or be normalized at the origin.

## Depends on

- [Open unit disk](../riemann-mapping-theorem/unit-disk.md).

## Proof depends on

- [Uniform inverse-square integral means](inverse-square-integral-means.md), for negative exponents via interpolation.

The positive-exponent range uses the growth bound for positive moments and area integration near the unit circle.

## Expansion

Separate normalization, positive moments, and interpolation of the inverse-square bound with the unit exponent-zero integrand. Check radial integrability for strict exponents and do not infer endpoint convergence.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/Brennan.lean#L47-L49) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/072.md).
- OpenAI, [univalent disk-map area integrability in the comparator proposition](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/Brennan.lean#L43-L45).
