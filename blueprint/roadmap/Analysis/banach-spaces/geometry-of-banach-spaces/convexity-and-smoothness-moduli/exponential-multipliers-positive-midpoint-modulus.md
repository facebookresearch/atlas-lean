# Positive midpoint modulus for exponential tree multipliers

Let $E_\mu$ be the [independent path-product space](independent-product-spaces-have-no-auc-renorming.md) for the rate-one exponential law. For $t>0$, its original norm has averaged cofinite modulus $H(t)=\inf_{\|x\|=1}\sup_F\inf_{y\in F,\|y\|\ge1}[(\|x+ty\|+\|x-ty\|)/2-1]$, with norm-closed finite-codimensional $F$. For a standard real Gaussian $G$,

$$0<\frac{7t}{480}\,\mathbb E[(|G|-20/t)_+]\le H(t).$$

## Depends on

- [The product-space model](independent-product-spaces-have-no-auc-renorming.md), the rate-one exponential law and the averaged (not one-sided) modulus.

## Proof depends on

- The exponential multiplier estimate with the Gaussian excess at the specified threshold, and positivity of that excess.

## Expansion

Separate the norm estimate from the Gaussian tail calculation. Retain the full range $t>0$ and the direction convention $\|y\|\ge1$.

## Sources

- OpenAI, [IndependentProducts comparator, main_exponential](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/IndependentProducts.lean#L95-L101).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/331.md).
