# Finite lower-head projections in a segment coordinate space

For a partially ordered set $V$, consider the [segment coordinate space](segment-coordinate-space.md) $X(V)\subseteq J(V)^*$ with coordinate vectors $e_v\in J(V)$ and coordinate functionals $e_v^*\in X(V)$. Let $H\subseteq V$ be a finite lower set: if $v\in H$ and $w\le v$, then $w\in H$. Use the maps on $X(V)$

$$P_Hx=\sum_{v\in H}x(e_v)e_v^*,\qquad Q_Hx=x-P_Hx.$$

Equivalently, $P_H$ is the restriction to the closed coordinate span of the map on $J(V)^*$ obtained by precomposition with the extension of the primal coordinate cut to $H$. Both projections are contractive: intersection of a segment with $H$ or with its complement leaves an order-convex chain, and disjoint tests remain disjoint on each cut. The finite sum takes values in the coordinate span, so subtraction defines $Q_H$ on the same space. The fixed-point conditions $x=P_Hx$ and $y=Q_Hy$ keep the head and tail respectively; the latter is equivalent to $y(e_v)=0$ for every $v\in H$.

## Depends on

- [Coordinate space of a segment-norm completion](segment-coordinate-space.md).

## Proof outline

Cutting each test segment into its part in the lower set and its part in the complementary upper set preserves order convexity and disjointness on each side. The resulting finite-vector cuts have norm at most one, so they extend to $J(V)$. Precomposition preserves contractivity on the dual; the finite coordinate formula restricts the head to $X(V)$, and subtraction restricts the tail to $X(V)$.

## Sources

- OpenAI, [segment cuts](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/ForestSpace/Segments.lean#L115-L135), [primal extensions and precomposition](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/ForestSpace/Projections.lean#L16-L83), [finite formula, restriction to the coordinate span and contractivity](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/ForestSpace/Projections.lean#L97-L149).
