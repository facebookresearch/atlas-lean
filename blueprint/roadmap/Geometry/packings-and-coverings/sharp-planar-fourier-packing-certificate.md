# Sharp Fourier certificate for planar circle packing

There exists a real radial Schwartz function $f$ on Euclidean $\mathbb R^2$ with $\widehat f(0)=1$, $f(0)=2/\sqrt3$, $\widehat f$ everywhere real and nonnegative, and $f(x)\leq0$ for every $|x|\geq1$. The Fourier convention is $\widehat f(\xi)=\int_{\mathbb R^2} f(x)e^{-2\pi i x\cdot\xi}\,dx$. This is an auxiliary-function existence result with the cutoff for radius-one-half disks, not merely a statement about the optimal packing density.

## Depends on
Real radial Schwartz functions and the precise Euclidean Fourier normalization, with the cutoff inclusive at distance one.

## Proof depends on
Construction of a sharp Fourier auxiliary function, verification of the exact two origin values, and uniform sign estimates on the entire tail and transform domain.

## Expansion
Separate the radial interpolation formula or certificate, the vanishing and sign verification, and the origin normalization. A preexisting density bound from geometric packing alone does not give this function, and no equality-case uniqueness is asserted.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PlanarPacking.lean#L35-L39) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/090.md).
