# Universal integral-means spectrum at exponent minus two

For injective holomorphic $f$ on the open unit disk with $f(0)=0$ and $f'(0)=1$, write $I_f(t,r)=(2\pi)^{-1}\int_{-\pi}^{\pi}|f'(re^{i\theta})|^t\,d\theta$. For each $t$ take the supremum, in the extended reals, over these $f$ of $\limsup_{r\to1^-}\log I_f(t,r)/\log(1/(1-r))$. At $t=-2$ that supremum equals $1$.

## Depends on

- [Normalized univalent functions](../hadamard-products-of-univalent-functions/class-s.md).

## Proof depends on

- [Uniform inverse-square integral means](inverse-square-integral-means.md), for the upper bound after letting the loss decrease to zero.

## Proof outline

For the lower bound use the normalized Koebe map $k(z)=z/(1-z)^2$, whose derivative is $(1+z)/(1-z)^3$. On the arc $|\theta-\pi|\le 1-r$, the numerator has size at most a constant times $1-r$ and the denominator is bounded away from zero for $r$ near one. This arc gives an inverse-square mean bounded below by a positive constant times $(1-r)^{-1}$. Use the linked uniform estimate with arbitrarily small positive loss for the other inequality of the extended-real limsup.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/Brennan.lean#L47-L49) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/072.md).
- OpenAI, [spectrum value in the comparator proposition](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/Brennan.lean#L37).
