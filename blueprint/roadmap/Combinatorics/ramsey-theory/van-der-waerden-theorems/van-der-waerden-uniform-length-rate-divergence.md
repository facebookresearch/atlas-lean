# Van der Waerden logarithmic length rates diverge uniformly in the color count

Let $W$ be the [van der Waerden forcing number](van-der-waerden-forcing-number.md). As the natural progression length $k$ tends to infinity, the real-valued sequence

$$
\inf_{r\in\mathbb N,\ r\ge2}\frac{\log(W(r,k):\mathbb R)}{(k:\mathbb R)\log(r:\mathbb R)}
$$

tends to $+\infty$. The infimum is in the reals, with $r$ varying inside the expression for each $k$; this is not merely divergence for each fixed $r$ separately. Logarithms are natural and real division at denominator zero is totalized, so the expression is defined even at $k=0$.

## Depends on

- [Van der Waerden forcing number](van-der-waerden-forcing-number.md).

## Proof depends on

- [Uniform superexponential lower bound for van der Waerden numbers](van-der-waerden-uniform-superexponential-lower-bound.md), with one threshold for all $r\ge2$. The floor of the base-two logarithm is at least half that logarithm for $r\ge2$, giving a common lower bound proportional to $\log k$ before taking the real infimum.

## Sources

- OpenAI, [Uniform real-infimum limit](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/ProgressionColoring/Main.lean#L40-L45) and [Derivation from the quantitative bound](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/ProgressionColoring/GrowthConsequences.lean#L9-L25).
