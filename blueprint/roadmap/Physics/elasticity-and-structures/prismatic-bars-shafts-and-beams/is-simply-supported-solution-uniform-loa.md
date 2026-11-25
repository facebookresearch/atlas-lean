# The uniform-load quartic solves the simply supported problem

Let $EI > 0$ and $L > 0$, and let $q$ be real. The
[uniform-load deflection](../euler-bernoulli-beam-under-uniform-load/uniform-load-deflection.md)

$$w(x) = \frac{q\, (L^3 x - 2L x^3 + x^4)}{24\, EI}$$

solves the [simply supported problem](is-simply-supported-solution.md): it is a polynomial, hence
four times continuously differentiable, $EI\, w''''(x) = q$ at every $x$, $w(0) = w(L) = 0$ and
$w''(0) = w''(L) = 0$.
