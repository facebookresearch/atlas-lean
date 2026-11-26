# Paired midpoint estimate for head and tail in a forest coordinate space

Let $V$ be a countably infinite partially ordered set such that each principal lower set $\{w:w\le v\}$ is a finite chain. In the [segment coordinate space](segment-coordinate-space.md) $X(V)$, let $H\subseteq V$ be any finite lower set and use the [head and tail projections](finite-lower-head-projections.md) $P_H,Q_H$. For all $x,y\in X(V)$ with $x=P_Hx$ and $y=Q_Hy$,

$$\sqrt{\|x\|^2+\|y\|^2/12}\le\frac{\|x+y\|+\|x-y\|}{2}.$$

There is no identification of $X(V)$ with the full dual in the hypotheses.

## Depends on

- [Coordinate space of a segment-norm completion](segment-coordinate-space.md).
- [Finite lower-head projections](finite-lower-head-projections.md).

## Expansion

Separate the paired correction for the primal segment tests from the dual norm estimate. For finite vectors $f,k$ of norm at most one supported on $H$ and its complement respectively, and for each $s>0$, construct one finite tail vector $c$ of norm at most one such that both signs satisfy

$$\|f+s(c\pm k)\|\le\sqrt{1+12s^2}.$$

The same $c$ is needed in both tests so that its evaluation cancels when the two dual estimates are added. The correction must control every disjoint-segment test, not just the two vectors' coordinate supports.

## Proof outline

Use ancestry to split disjoint tests and finite ancestor chains to control the paired correction. The dual test lemma uses a common tail correction and a positive scalar weight to bound the weighted sum of the two functional evaluations. Optimizing that weight (with the zero cases handled directly) gives the quadratic form above. The fixed-point conditions supply precisely the two annihilation hypotheses, and the norms on the coordinate span are the inherited operator norms.

## Sources

- OpenAI, [general-forest statement, first conjunct](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/ForestSpace/Main.lean#L29-L36), [proof on the coordinate span](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/ForestSpace/Projections.lean#L214-L225), [dual test and optimized estimate](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/ForestSpace/Polar.lean#L77-L157).
- OpenAI, [*Asymptotic midpoint uniform convexity and unbounded diamond distortion in a reflexive tree space*, §4.1](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Asymptotic-midpoint-uniform-convexity-and-unbounded-diamond-distortion-in-a-reflexive-tree-space-September-27-2026/manuscript.pdf); [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/331.md).
