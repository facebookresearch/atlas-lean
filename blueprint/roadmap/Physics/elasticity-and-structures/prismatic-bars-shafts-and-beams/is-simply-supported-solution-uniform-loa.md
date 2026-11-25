# The uniform-load quartic solves the simply supported problem

Let $EI > 0$ and $L > 0$, and let $q$ be real. The
[uniform-load deflection](../euler-bernoulli-beam-under-uniform-load/uniform-load-deflection.md)

$$w(x) = \frac{q\, (L^3 x - 2L x^3 + x^4)}{24\, EI}$$

solves the [simply supported problem](is-simply-supported-solution.md): it is a polynomial, hence
four times continuously differentiable, $EI\, w''''(x) = q$ at every $x$, $w(0) = w(L) = 0$ and
$w''(0) = w''(L) = 0$.

The beam equation and the four conditions are the uniform-load results: the
[beam equation](../euler-bernoulli-beam-under-uniform-load/uniform-load-deflection-ei-mul-iterated.md),
zero deflection at the [left](../euler-bernoulli-beam-under-uniform-load/uniform-load-deflection-zero-left.md)
and [right](../euler-bernoulli-beam-under-uniform-load/uniform-load-deflection-zero-right.md)
supports, and zero second derivative at the
[left](../euler-bernoulli-beam-under-uniform-load/uniform-load-deflection-second-deriv-zer.md) and
[right](../euler-bernoulli-beam-under-uniform-load/uniform-load-deflection-second-deriv-zer-2.md)
supports.
