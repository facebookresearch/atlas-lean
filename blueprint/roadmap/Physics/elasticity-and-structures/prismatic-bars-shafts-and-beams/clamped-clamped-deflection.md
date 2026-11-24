# Deflection of a clamped-clamped beam under a uniform load

For real numbers $EI$, $L$, $q$ and $x$, the clamped-clamped deflection is

$$w(x) = \frac{q\, x^2\, (L - x)^2}{24\, EI}.$$

It models the deflection of an Euler–Bernoulli beam of length $L$ and bending stiffness $EI$,
clamped at both ends, under the uniform distributed load $q$: for $EI > 0$, $L > 0$ and $q \ne 0$ it
satisfies $EI\, w'''' = q$ with zero deflection and zero slope at $x = 0$ and $x = L$
([clamped slopes change the solution](clamped-slopes-change-solution.md)). At midspan
$w(L/2) = q L^4/(384\, EI)$. In the physical reading $EI > 0$, $L > 0$ and $x \in [0, L]$; with the
convention $a/0 = 0$ the formula is $0$ when $EI = 0$.
