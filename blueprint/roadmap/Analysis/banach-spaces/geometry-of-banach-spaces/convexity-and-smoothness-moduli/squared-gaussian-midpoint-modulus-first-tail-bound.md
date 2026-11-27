# First squared-Gaussian tail bound for the midpoint modulus

Let $E_\mu$ be the [independent path-product space](independent-product-spaces-have-no-auc-renorming.md) for the law of $G^2$, with $G$ standard real Gaussian. For every $t>0$ its [averaged modulus](exponential-multipliers-positive-midpoint-modulus.md), with directions of norm at least one and the inherited $L^1$ norm, satisfies

$$0<\tfrac18\Pr(|G|\ge4\sqrt2(2+\sqrt2)/t)\le H(t).$$

## Depends on

- The squared-Gaussian product law and the specified averaged cofinite modulus.

## Proof depends on

- The first squared-Gaussian norm estimate with threshold $4\sqrt2(2+\sqrt2)/t$, and positivity of the Gaussian tail.

## Expansion

Establish the finite-coordinate estimate with its exact prefactor before extending to the completed space. Do not exchange the Gaussian tail with the squared-Gaussian tail in the conclusion.

## Sources

- OpenAI, [IndependentProducts comparator, main_gaussian_24](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/IndependentProducts.lean#L102-L108).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/331.md).
