# Strict bounded spectrum bound at minus one and failure of Kraetzer's formula

For an injective holomorphic map $f$ on the open disk with $f(0)=0$, $f'(0)=1$ and bounded image, set $I_f(t,r)=(2\pi)^{-1}\int_{-\pi}^{\pi}|f'(re^{i\theta})|^t\,d\theta$. Let $B_b(t)$ be the extended-real supremum over such $f$ of $\limsup_{r\to1^-}\log I_f(t,r)/\log(1/(1-r))$. Then $B_b(-1)<1/4$. In particular the formula $B_b(t)=t^2/4$ for $|t|\leq2$ and $B_b(t)=|t|-1$ otherwise cannot hold for all real $t$.

## Depends on

- [Normalized univalent functions](../hadamard-products-of-univalent-functions/class-s.md).

## Proof depends on

- [Strict inverse-first-power integral-means estimate](inverse-first-power-integral-means.md).

## Proof strategy

Formalize the limsup bound in the extended reals with the same positive gap before taking the supremum over bounded maps. Then evaluate the proposed formula at $-1$; no formula for the rest of the spectrum is asserted.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/StrictMeans.lean#L34-L42) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/072.md).
