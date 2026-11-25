# The cantilever polynomial solves the clamped-free problem

Let $EI > 0$ and $L > 0$, and let $q$ and $P$ be real. The
[cantilever deflection](cantilever-deflection.md)

$$w(x) = \frac{q\, x^2\, (6L^2 - 4Lx + x^2)}{24\, EI} + \frac{P\, x^2\, (3L - x)}{6\, EI}$$

solves the [clamped-free cantilever problem](is-cantilever-solution.md): it is a polynomial, hence
four times continuously differentiable, $EI\, w''''(x) = q$ at every $x$, $w(0) = w'(0) = 0$,
$EI\, w''(L) = 0$ and $-EI\, w'''(L) = P$.
