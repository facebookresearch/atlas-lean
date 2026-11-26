# Directional Hilbert truncations at a reciprocal Lipschitz scale

There is a real $C>0$ such that for any real $K>0$, $0<\epsilon\leq R\leq 1/(10^6 K)$, $K$-Lipschitz unit vector field $v$ on Euclidean $\mathbb R^2$, and complex Schwartz function $f$, the $L^2$ norm of $x\mapsto\int_\epsilon^R (f(x-tv(x))-f(x+tv(x)))\,dt/t$ is at most $C\|f\|_2$. The case $\epsilon=R$ is included. Both coordinates of $x$ may enter the field.

## Depends on

Real interval integration of the complex-valued symmetric difference, Euclidean Lipschitz bound, and the nonnegative $L^2$ norms.

## Proof depends on

The finite-rectangle weak $(2,2)$ bound for the Lipschitz Kakeya maximal operator and martingale variation control, followed by a uniform normalized short-truncation estimate with cutoff $10^{-6}$.

## Expansion

Separate the rectangle maximal estimate and variation bound from time-frequency recombination for unit Lipschitz fields, tracking the permitted $10^{-6}$ cutoff. Then dilate both the field and the $L^2$ norm. Preserve $\epsilon=R$ and do not infer the numerical cutoff from the existence of an unspecified positive scale.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/LipschitzHilbert.lean#L67-L75) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/083.md).
