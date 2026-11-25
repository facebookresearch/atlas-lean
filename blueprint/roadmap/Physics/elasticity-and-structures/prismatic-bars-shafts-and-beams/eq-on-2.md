# Uniqueness for the clamped-free cantilever problem

Let $EI > 0$. If $w$ solves the [clamped-free cantilever problem](is-cantilever-solution.md) with
bending stiffness $EI$, span $L$, uniform load $q$ and tip force $P$, then for every $x \in [0, L]$

$$w(x) = \frac{q\, x^2\, (6L^2 - 4Lx + x^2)}{24\, EI} + \frac{P\, x^2\, (3L - x)}{6\, EI},$$

the [cantilever deflection](cantilever-deflection.md). Outside $[0, L]$, $w$ is not determined.

Proof: the difference $d$ of $w$ and the polynomial is four times continuously differentiable with
$d'''' = 0$ on $(0, L)$, so it is a cubic on $[0, L]$; the four end conditions $d(0) = d'(0) = 0$
and $d''(L) = d'''(L) = 0$ make its coefficients vanish.
