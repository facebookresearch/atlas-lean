# Goemans–Williamson Lemma 3.2: probability that a random hyperplane separates two unit vectors

For unit vectors $u, v \in \mathbb{R}^n$ and a standard Gaussian vector $r$,

$$\Pr[\operatorname{sgn}(u \cdot r) \ne \operatorname{sgn}(v \cdot r)] = \frac{\arccos(u \cdot v)}{\pi},$$

with $\operatorname{sgn} x = 1$ for $x \ge 0$ and $-1$ otherwise. Goemans and Williamson state the
lemma for $r$ uniform on the unit sphere and prove it by symmetry: the set of $r$ with
$u \cdot r \ge 0 > v \cdot r$ meets the sphere in a spherical digon of angle
$\theta = \arccos(u \cdot v)$. They remark (p. 1121) that $r$ may be taken Gaussian without
normalization, since normalizing does not change the signs; the statement above is that
Gaussian form.

## Informally uses

- [Separation probability in an inner product space](../../../Probability/distributions/continuous/multivariate-normal-distribution/std-gaussian-sign-ne.md):
  the same statement in any finite-dimensional real inner product space, proved by reduction to
  the plane and polar coordinates rather than by the paper's spherical-digon argument.

For $u \cdot v = \rho \in (-1, 1)$ the pair $(u \cdot r, v \cdot r)$ is a standard bivariate normal
vector with correlation $\rho$, so the lemma is equivalent to Sheppard's quadrant formula.

## Sources

- M. X. Goemans and D. P. Williamson, "Improved approximation algorithms for maximum cut and satisfiability problems using semidefinite programming", *J. ACM* 42(6) (1995), 1115–1145 (journal version), Lemma 3.2 and p. 1121.
