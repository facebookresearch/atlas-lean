# Kakeya maximal estimate with every positive power loss

For a unit vector $\omega\in\mathbb R^n$, center $x$, and $0<\delta\leq1$, let $T_\delta(\omega,x)$ be the union of open Euclidean radius-$\delta$ balls centered at $x+t\omega$ for $-1/2\leq t\leq1/2$. Define $K_\delta f(\omega)=\sup_x |T_\delta(\omega,x)|^{-1}\int_{T_\delta(\omega,x)} |f|$, with nonnegative integrals and extended-real supremum. For every integer $n\geq2$ and $\varepsilon>0$ there is $C>0$ such that for every $0<\delta\leq1$ and complex $f\in L^n(\mathbb R^n)$, the output belongs to $L^n(\sigma)$ and $\|K_\delta f\|_{L^n(\sigma)}\leq C\delta^{-\varepsilon}\|f\|_n$, where $\sigma$ is the polar surface measure of the Euclidean unit sphere.

## Depends on

A tube is a neighborhood of the whole segment, including both ends; use the volume of that actual open tube in its average.

## Proof depends on

Uniform directional packing estimates for arbitrarily small tubes and recovery of the estimate for a supremum over centers.

## Expansion

Separate finite-direction tube bounds, passage to the directional surface integral, and measurability of the center supremum by continuity or a justified dense subfamily. Verify the scale power applies over the whole interval $(0,1]$.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/LocalSmoothing.lean#L119-L127) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/079.md).
