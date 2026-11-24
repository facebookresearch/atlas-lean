# Uniqueness for the simply supported beam under a uniform load

Let $EI > 0$. If $w$ solves the [simply supported problem](is-simply-supported-solution.md) with
bending stiffness $EI$, span $L$ and uniform load $q$, then for every $x \in [0, L]$

$$w(x) = \frac{q\, (L^3 x - 2L x^3 + x^4)}{24\, EI},$$

the
[uniform-load deflection](../euler-bernoulli-beam-under-uniform-load/uniform-load-deflection.md).
Outside $[0, L]$, $w$ is not determined.

Proof: the difference of $w$ and the quartic has zero fourth derivative on $(0, L)$, so it is a
cubic on $[0, L]$, and the two deflection and two curvature conditions make its coefficients vanish.
