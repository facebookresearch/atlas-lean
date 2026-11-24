# Deflection of a cantilever under a uniform load and a tip force

For real numbers $EI$, $L$, $q$, $P$ and $x$, the cantilever deflection is

$$w(x) = \frac{q\, x^2\, (6L^2 - 4Lx + x^2)}{24\, EI} + \frac{P\, x^2\, (3L - x)}{6\, EI}.$$

It is the deflection of an Euler–Bernoulli beam of length $L$ and bending stiffness $EI$, clamped at
$x = 0$ and free at $x = L$, under the uniform distributed load $q$ and the tip force $P$, with $w$,
$q$ and $P$ positive in the same transverse direction: for $EI > 0$ and $L > 0$ it
[solves the clamped-free problem](is-cantilever-solution-cantilever-deflec.md) and
[every solution equals it](eq-on-2.md) on $[0, L]$. At the free end it gives
$w(L) = q L^4/(8\, EI) + P L^3/(3\, EI)$. In the physical reading $EI > 0$, $L > 0$ and
$x \in [0, L]$; the formula is defined for all real inputs, and with the convention $a/0 = 0$ it is
$0$ when $EI = 0$.
