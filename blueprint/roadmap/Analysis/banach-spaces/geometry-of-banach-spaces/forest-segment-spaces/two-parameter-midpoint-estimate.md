# Two-parameter midpoint estimate in a forest coordinate space

Let $V$ be a countably infinite partially ordered set in which each principal lower set is a finite chain. Use the [segment coordinate space](segment-coordinate-space.md) $X(V)$ and the [projections](finite-lower-head-projections.md) $P_H,Q_H$ for an arbitrary finite lower set $H$. For every $x,y\in X(V)$ satisfying $x=P_Hx$ and $y=Q_Hy$, and every pair of real numbers $s,t>0$,

$$\frac{\|x\|+st\|y\|}{\sqrt{1+12s^2}}\le\frac{\|x+ty\|+\|x-ty\|}{2}.$$

## Depends on

- [Coordinate space of a segment-norm completion](segment-coordinate-space.md).
- [Finite lower-head projections](finite-lower-head-projections.md).

## Proof depends on

- [Paired midpoint estimate for head and tail](paired-midpoint-estimate.md).

## Proof outline

The paired estimate applies to $x$ and $ty$, since the tail projection is linear. Apply the two-dimensional Cauchy–Schwarz inequality to $(\|x\|,t\|y\|/\sqrt{12})$ and $(1,\sqrt{12}s)$, and divide by $\sqrt{1+12s^2}$. This route does not require an independent two-parameter dual test once the paired estimate is available.

## Sources

- OpenAI, [general-forest statement, second conjunct](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/ForestSpace/Main.lean#L32-L41), [two-parameter proof on the coordinate span](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/ForestSpace/Projections.lean#L227-L239).
- OpenAI, [*Asymptotic midpoint uniform convexity and unbounded diamond distortion in a reflexive tree space*, §§4 and 4.1](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Asymptotic-midpoint-uniform-convexity-and-unbounded-diamond-distortion-in-a-reflexive-tree-space-September-27-2026/manuscript.pdf); [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/331.md).
