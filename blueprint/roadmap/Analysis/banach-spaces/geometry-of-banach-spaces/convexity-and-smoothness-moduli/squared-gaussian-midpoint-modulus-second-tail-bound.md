# Second squared-Gaussian tail bound for the midpoint modulus

Let $E_\mu$ be the [independent path-product space](independent-product-spaces-have-no-auc-renorming.md) for the law of $G^2$, with $G$ standard real Gaussian. For every $t>0$ its [averaged modulus](exponential-multipliers-positive-midpoint-modulus.md), with directions of norm at least one and the inherited $L^1$ norm, satisfies

$$0<\tfrac14\Pr(|G|\ge8\sqrt6/t)\le H(t).$$

## Depends on

- The squared-Gaussian product law and the specified averaged cofinite modulus.

## Proof depends on

- The second squared-Gaussian norm estimate with threshold $8\sqrt6/t$, and positivity of the Gaussian tail.

## Expansion

Isolate the separate tail estimate with its $1/4$ prefactor, then pass it through the cofinite quantifiers. The first tail bound does not subsume this exact assertion.

## Sources

- OpenAI, [IndependentProducts comparator, main_gaussian_12](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/IndependentProducts.lean#L109-L115).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/331.md).
