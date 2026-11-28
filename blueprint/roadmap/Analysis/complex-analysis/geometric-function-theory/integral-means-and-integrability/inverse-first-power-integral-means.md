# Strict inverse-first-power integral-means estimate

Write $\mathcal S$ for the injective holomorphic maps of the open disk to the complex plane with $f(0)=0$ and $f'(0)=1$, and set $I_f(t,r)=(2\pi)^{-1}\int_{-\pi}^{\pi}|f'(re^{i\theta})|^t\,d\theta$. There are real constants $\varepsilon,C$, with $0<\varepsilon<1/4$, such that $I_f(-1,r)\leq C(1-r)^{-1/4+\varepsilon}$ for all $f\in\mathcal S$ and $1/2\leq r<1$. There is no boundedness or boundary regularity assumption on $f$.

## Depends on

- [Normalized univalent functions](../hadamard-products-of-univalent-functions/class-s.md).

## Proof depends on

The source needs a uniform strict improvement below the growth exponent $1/4$; a bound with an arbitrarily small positive loss *above* $1/4$ does not suffice.

## Expansion

Isolate the strict inverse-first-power bound and its constants, including the dependence on normalized univalence and the full radial interval. The spectrum comparison uses this estimate as a separate step.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/StrictMeans.lean#L34-L42) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/072.md).
