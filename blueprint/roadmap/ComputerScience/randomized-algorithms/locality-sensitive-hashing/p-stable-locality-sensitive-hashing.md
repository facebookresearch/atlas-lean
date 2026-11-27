# p-stable LSH collision probabilities for p = 2 and p = 1

For a projection vector $a$, a width $w > 0$ and a shift $b$ uniform on $[0, w)$, let $h_{a,b}(v) = \lfloor(\langle a, v\rangle + b)/w\rfloor$. Conditioned on $a$, two projections $x, y$ collide with probability $\max(0, 1 - |x - y|/w)$. If $\langle a, u - v\rangle$ has the law of $c\,Z$ with $Z \sim \mu$, the collision probability is $\int \max(0, 1 - c|z|/w)\,d\mu(z)$.

($p = 2$.) With $a$ standard Gaussian on a finite-dimensional real inner product space and $c = \|u - v\|_2$, the collision probability is $p_2(c) = \int_0^w \frac{2}{c}\varphi(t/c)(1 - t/w)\,dt$ with $\varphi$ the standard normal density, which equals $\Pr[|Z| \le w/c] - \frac{2c}{\sqrt{2\pi}\,w}(1 - e^{-w^2/(2c^2)})$.

($p = 1$.) With i.i.d. standard Cauchy coordinates, $\langle a, u - v\rangle$ is Cauchy with scale $c = \|u - v\|_1$ (Cauchy $1$-stability) and the collision probability is $p_1(c) = \frac{2}{\pi}\arctan(w/c) - \frac{c}{\pi w}\ln(1 + w^2/c^2)$.

Both $p_1$ and $p_2$ are strictly positive and strictly decreasing in $c$, so the families are locality sensitive for $\ell_1$ and $\ell_2$ distance.

## Proof sketch

For fixed projections, the floors of $x + b$ and $y + b$ at width $w$ agree exactly when no multiple of $w$ falls between them, an interval of length $|x - y|$. Fubini integrates over the projection, and stability turns $\langle a, u - v\rangle$ into a scaled standard variable; the closed forms are elementary integrals of the Gaussian and Cauchy densities.

## Depends on

- [Locality-sensitive hash families](locality-sensitive-hash-families.md)
- [Gaussian measures are stable of index 2](../../../Probability/infinite-divisibility-regular-variation/stable-distributions-and-domains-of-attraction/is-stable-gaussian-real.md)

## Proof depends on

- [Gaussian measures are stable of index 2](../../../Probability/infinite-divisibility-regular-variation/stable-distributions-and-domains-of-attraction/is-stable-gaussian-real.md)

## Sources

- M. Datar, N. Immorlica, P. Indyk and V. S. Mirrokni, "Locality-Sensitive Hashing Scheme Based on p-Stable Distributions", Proceedings of the 20th Symposium on Computational Geometry, 2004.
