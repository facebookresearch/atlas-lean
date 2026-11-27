# A random hyperplane separates two unit vectors with probability angle over π

Let $r$ be a standard Gaussian vector in a finite-dimensional real inner product space and $u$,
$v$ unit vectors. Then

$$\Pr\left[\operatorname{sgn}\langle u, r\rangle \ne \operatorname{sgn}\langle v, r\rangle\right] = \frac{\arccos \langle u, v\rangle}{\pi},$$

with $\operatorname{sgn} x = 1$ for $x \ge 0$. This is the Gaussian form of Lemma 3.2 of Goemans
and Williamson, whose remark on p. 1121 says that a Gaussian direction gives the same signs as a
uniform point on the sphere. The proof writes $u = c e_1 - s e_2$ and $v = c e_1 + s e_2$ with
$e_1 = (u + v)/\|u + v\|$, $e_2 = (v - u)/\|v - u\|$, $c = \cos a$, $s = \sin a$, so that
$2a = \arccos\langle u, v\rangle$, and then uses the planar computation. The cases $v = u$
(probability $0$) and $v = -u$ (probability $1$, because $\langle u, r\rangle = 0$ has probability $0$)
are treated separately.

## Informally uses

- [Two-dimensional marginal of the standard Gaussian](map-inner-pair-std-gaussian.md): reduction
  to the plane spanned by $u$ and $v$.
- [The planar wedge probability](gaussian-real-prod-wedge.md): the computation in that plane.
- [One-dimensional marginal of the standard Gaussian](map-inner-std-gaussian.md): the case
  $v = -u$.

For a standard bivariate normal pair with correlation $\rho = \langle u, v\rangle \in (-1, 1)$ this is
equivalent to Sheppard's formula, since
$1 - 2\left(\frac14 + \frac{\arcsin \rho}{2\pi}\right) = \frac{\arccos \rho}{\pi}$; Sheppard's formula is deduced from this
page through the quadrant probability for two directions.

## Sources

- M. X. Goemans and D. P. Williamson, "Improved approximation algorithms for maximum cut and satisfiability problems using semidefinite programming", *J. ACM* 42(6) (1995), 1115–1145 (journal version), Lemma 3.2 and p. 1121.
