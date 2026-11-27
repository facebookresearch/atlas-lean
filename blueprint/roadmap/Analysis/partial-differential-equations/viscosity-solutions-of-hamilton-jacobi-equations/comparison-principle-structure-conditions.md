# Comparison principle for first-order equations

Let $\Omega$ be a bounded open subset of a finite-dimensional real inner
product space and $F$ continuous on $\overline\Omega \times \mathbb{R} \times E^*$, with

- (3.13) $\gamma(r - s) \le F(x, r, p) - F(x, s, p)$ for $r \ge s$ and $x \in \overline\Omega$, for some $\gamma > 0$;
- (3.14) $F(y, r, \alpha\langle x - y, \cdot\rangle) - F(x, r, \alpha\langle x - y, \cdot\rangle) \le \omega(\alpha|x - y|^2 + |x - y|)$
  for $x, y \in \Omega$, $r \in \mathbb{R}$, $\alpha > 0$, where $\omega \ge 0$ and $\omega(0+) = 0$.

If $u$ is upper semicontinuous on $\overline\Omega$ and a viscosity subsolution, $v$ lower
semicontinuous on $\overline\Omega$ and a viscosity supersolution of $F = 0$ on $\Omega$, and
$u \le v$ on $\partial\Omega$, then $u \le v$ on $\Omega$.

This is Theorem 3.3 of the user's guide for an $F$ that does not depend on the Hessian. The
[continuous case](comparison-principle-continuous-case.md) is the special case of $u$ and $v$
continuous on $\overline\Omega$; for semicontinuous $u$ and $v$ the proof must locate the
maximisers through limit points rather than moduli of continuity.

## Sources

- M. G. Crandall and P.-L. Lions, "Viscosity solutions of Hamilton–Jacobi equations", Trans. Amer. Math. Soc. 277 (1983), 1–42.
- M. G. Crandall, H. Ishii and P.-L. Lions, "User's guide to viscosity solutions of second order partial differential equations", Bull. Amer. Math. Soc. 27 (1992), 1–67, arXiv:math/9207212, Lemma 3.1 and Theorem 3.3.
