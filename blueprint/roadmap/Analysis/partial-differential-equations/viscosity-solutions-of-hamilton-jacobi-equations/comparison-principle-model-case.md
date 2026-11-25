# Comparison principle for $\gamma u + H(Du) = f(x)$

Let $\Omega$ be a bounded open subset of a finite-dimensional real inner product space, $\gamma > 0$,
$H$ any function of the gradient, and $f$ continuous on $\overline\Omega$. If $u$ is a viscosity
subsolution and $v$ a viscosity supersolution of $\gamma u + H(Du) - f(x) = 0$ on $\Omega$, both
continuous on $\overline\Omega$, and $u \le v$ on $\partial\Omega$, then $u \le v$ on $\Omega$.

This is the model first-order case (Example 3.6) of the comparison theorem 3.3 of the user's guide,
proved by its doubling of variables. If $u - v$ had a positive maximum $\delta$, maximise
$u(x) - v(y) - \frac{\alpha}{2}|x - y|^2$ over $\overline\Omega \times \overline\Omega$. For $\alpha$ large
the maximiser $(\hat x, \hat y)$ is interior and $|\hat x - \hat y|$ is small (Lemma 3.1). The test
functions $v(\hat y) + \frac{\alpha}{2}|x - \hat y|^2$ at $\hat x$ and $u(\hat x) - \frac{\alpha}{2}|\hat x - y|^2$
at $\hat y$ have the same gradient $p = \alpha(\hat x - \hat y)$, so subtracting the two viscosity
inequalities eliminates $H(p)$ and leaves
$\gamma\delta \le \gamma(u(\hat x) - v(\hat y)) \le f(\hat x) - f(\hat y)$, which is small by uniform
continuity of $f$. The proof here chooses one large $\alpha$ quantitatively from the moduli of
continuity of $u$, $v$ and $f$, instead of letting $\alpha \to \infty$.

Theorem 3.3 itself covers $x$-dependent $F$ under the structure conditions (3.13)–(3.14), in the
[continuous case](comparison-principle-continuous-case.md), as well as semicontinuous
$u, v$ ([semicontinuous case](comparison-principle-structure-conditions.md)) and second-order equations.

## Background

- [Classical solutions are viscosity solutions](is-viscosity-solution-of-classical.md): with it,
  the theorem compares classical sub- and supersolutions too, the classical maximum principle being
  the motivation of §3 of the user's guide.

## Sources

- M. G. Crandall and P.-L. Lions, "Viscosity solutions of Hamilton–Jacobi equations", Trans. Amer. Math. Soc. 277 (1983), 1–42.
- M. G. Crandall, H. Ishii and P.-L. Lions, "User's guide to viscosity solutions of second order partial differential equations", Bull. Amer. Math. Soc. 27 (1992), 1–67, arXiv:math/9207212, Lemma 3.1, Theorem 3.3 and Example 3.6.
