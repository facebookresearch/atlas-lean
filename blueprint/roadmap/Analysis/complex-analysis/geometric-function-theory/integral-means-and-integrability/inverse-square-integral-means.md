# Uniform inverse-square integral means on the disk

Let $\mathcal S$ consist of injective holomorphic $f$ on the open unit disk with $f(0)=0$ and $f'(0)=1$. Set $I_f(t,r)=(2\pi)^{-1}\int_{-\pi}^{\pi}|f'(re^{i\theta})|^t\,d\theta$. For every $\varepsilon>0$ there is a real constant $C$ independent of $f\in\mathcal S$ and $1/2\leq r<1$ such that $I_f(-2,r)\leq C(1-r)^{-1-\varepsilon}$.

## Depends on

- [Normalized univalent functions](../hadamard-products-of-univalent-functions/class-s.md).

## Proof depends on

The uniform negative-moment estimate controlling derivatives as the circle approaches the boundary, with one constant over the entire normalized class.

## Expansion

Isolate the inverse-square estimate for the source's boundary-scale decomposition and its summation with exponent loss $\varepsilon$. Separate this estimate from the consequences about extended-real growth exponents and area integrability.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/Brennan.lean#L47-L49) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/072.md).
- OpenAI, [uniform inverse-square bound in the comparator proposition](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/Brennan.lean#L33-L36).
