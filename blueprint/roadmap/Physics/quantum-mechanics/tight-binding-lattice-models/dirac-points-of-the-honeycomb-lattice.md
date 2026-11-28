# Dirac points of the honeycomb lattice

The two honeycomb bands touch at zero energy at the zone corners $K$ and $K'$, where the dispersion is linear with velocity $3ta/2$.

With $f$ and $E_\pm$ as in the honeycomb tight-binding bands and the corners
$K = (\tfrac{2\pi}{3a}, \tfrac{2\pi}{3\sqrt{3}a})$, $K' = (\tfrac{2\pi}{3a}, -\tfrac{2\pi}{3\sqrt{3}a})$,
one has $f(K) = f(K') = -3$, hence $E_+(K) = E_-(K) = 0$ and likewise at $K'$. For fixed $a, t > 0$ and $q \to 0$,

$$
E_\pm(K + q) = \pm v_F|q| + O(|q|^2), \qquad v_F = \frac{3ta}{2},
$$

and the same holds at $K'$; here $\hbar = 1$, and when $q$ is a wavevector the physical group velocity is
$3ta/(2\hbar)$. The statement concerns these two corners only; it does not assert that they are the only zeros of
$3 + f$ modulo the reciprocal lattice.

## Context

Graduate level. Linear band crossings of this kind are predicted for ideal honeycomb π–d conjugated frameworks; whether a given MOF shows them depends on its actual band structure.

## Depends on

- [Honeycomb tight-binding bands](honeycomb-tight-binding-bands.md)

## Proof depends on

None.

## Expansion

At $K$, $\cos(\sqrt{3}k_ya) = \cos(2\pi/3) = -1/2$, $\cos(\tfrac{\sqrt{3}}{2}k_ya) = \cos(\pi/3) = 1/2$
and $\cos(\tfrac32k_xa) = \cos\pi = -1$, so $f(K) = -1 - 2 = -3$. Taylor expansion gives
$X(q) = 3 + f(K+q) = \tfrac{9a^2}{4}|q|^2 + O(|q|^3)$. For $q \ne 0$,
$|\sqrt{X} - \tfrac{3a}{2}|q|| = |X - \tfrac{9a^2}{4}|q|^2|/(\sqrt{X} + \tfrac{3a}{2}|q|) \le O(|q|^3)/(\tfrac{3a}{2}|q|) = O(|q|^2)$,
which gives the linear term without differentiating the square root at zero.

## Sources

- A. H. Castro Neto, F. Guinea, N. M. R. Peres, K. S. Novoselov and A. K. Geim, "The electronic properties of graphene", *Reviews of Modern Physics* 81, 109–162 (2009), [doi.org](https://doi.org/10.1103/RevModPhys.81.109); equation numbers from arXiv:0709.1163v2, Eqs. (3), (6) and (7).
