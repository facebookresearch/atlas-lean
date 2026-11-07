# Real numbers with a common continued fraction prefix are close

Let $\xi$ and $\xi'$ be
real numbers with continued fraction expansions $[a_0; a_1, a_2, \dots]$ and
$[a_0'; a_1', a_2', \dots]$, computed by $\xi_0 = \xi$, $a_i = \lfloor \xi_i \rfloor$ and
$\xi_{i+1} = 1/(\xi_i - a_i)$, stopping when $\xi_i = a_i$ (so an expansion is finite exactly when
the number is rational). Let $k \ge 0$ be an integer, and suppose that $a_0 = a_0'$ and that for
each $1 \le i \le k$ either both expansions have a digit of index $i$ and $a_i = a_i'$, or neither
has one. Then $|\xi - \xi'| \le 2^{1-k}$.

## Sources

- Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47, Lemma 5 (`integers-2025-A47-lem-5`), quoted from Cusick and Flahive, Lemma 1.
