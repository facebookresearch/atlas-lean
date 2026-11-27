# Volume lemma of the ellipsoid method

For $n \ge 2$, a positive definite $A$, a centre $a$ and $c \ne 0$,

$$
\mathrm{vol}\, E(a', A') < e^{-1/(2(n+1))}\, \mathrm{vol}\, E(a, A),
$$

where $E(a', A')$ is the ellipsoid of the central-cut step, which [contains the half-ellipsoid](half-ellipsoid-subset-next-ellipsoid.md) $E(a, A) \cap \{c^\top x \le c^\top a\}$. It combines the [exact volume factor](volume-next-ellipsoid.md) with its [bound by the exponential](volume-ratio-lt-exp.md); strictness uses $0 < \mathrm{vol}\, E(a, A) < \infty$, which holds because the unit ball has [positive](volume-unit-ellipsoid-pos.md) and [finite](volume-unit-ellipsoid-lt-top.md) volume.

## Sources

- M. X. Goemans, *Lecture notes on the ellipsoid algorithm*, MIT 18.433 Combinatorial Optimization, Handout 19 (4 May 2009), <https://math.mit.edu/~goemans/18433S09/ellipsoid.pdf>, Lemma 7.1 and Claim 7.2.
