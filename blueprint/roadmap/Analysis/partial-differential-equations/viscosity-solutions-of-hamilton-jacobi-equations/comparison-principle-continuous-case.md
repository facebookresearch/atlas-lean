# Comparison principle for first-order equations, continuous case

Let $\Omega$ be a bounded open subset of a finite-dimensional real inner product space, $\gamma > 0$,
and let $F(x, r, p)$ satisfy

- (3.13) $\gamma(r - s) \le F(x, r, p) - F(x, s, p)$ for $r \ge s$ and $x \in \overline\Omega$;
- (3.14) $F(y, r, \alpha\langle x - y, \cdot\rangle) - F(x, r, \alpha\langle x - y, \cdot\rangle) \le \omega(\alpha|x - y|^2 + |x - y|)$
  for $x, y \in \Omega$, $r \in \mathbb{R}$ and $\alpha > 0$, where $\omega(t) \to 0$ as $t \to 0^+$.

As printed in the user's guide (p. 18), (3.13) is asked on $\overline\Omega$ and (3.14) on $\Omega$.

If $u$ is a viscosity subsolution and $v$ a viscosity supersolution of $F = 0$ on $\Omega$, both
continuous on $\overline\Omega$, and $u \le v$ on $\partial\Omega$, then $u \le v$ on $\Omega$.

This is Theorem 3.3 of the user's guide for first-order equations and continuous sub- and
supersolutions, with its proof. Maximise $\Phi_\alpha(x, y) = u(x) - v(y) - \frac{\alpha}{2}|x - y|^2$ over
$\overline\Omega^2$, with maximal value $M_\alpha$ at $(x_\alpha, y_\alpha)$. Both test functions have
gradient $p = \alpha\langle x_\alpha - y_\alpha, \cdot\rangle$, so

$$\gamma\delta \le F(x_\alpha, u, p) - F(x_\alpha, v, p) \le F(y_\alpha, v, p) - F(x_\alpha, v, p) \le \omega(\alpha|x_\alpha - y_\alpha|^2 + |x_\alpha - y_\alpha|),$$

where $\delta > 0$ is the assumed positive value of $u - v$. Unlike the
[model case](comparison-principle-model-case.md), the right-hand side needs
$\alpha|x_\alpha - y_\alpha|^2 \to 0$ (Lemma 3.1 (i)). The proof here gets it quantitatively: since
$M_\alpha \ge M_{2\alpha} + \frac{\alpha}{2}|x_{2\alpha} - y_{2\alpha}|^2$ and $M$ is bounded, the decrements
$M_{\alpha_0 2^k} - M_{\alpha_0 2^{k+1}}$ telescope, so one of the first $N$ is at most $\sup|u| + \sup|v|$ over $N$.
No continuity of $F$ is used.

Theorem 3.3 also treats semicontinuous $u$ and $v$, and second-order equations; the first-order
semicontinuous statement is [stated separately](comparison-principle-structure-conditions.md).

## Sources

- M. G. Crandall and P.-L. Lions, "Viscosity solutions of Hamilton–Jacobi equations", Trans. Amer. Math. Soc. 277 (1983), 1–42.
- M. G. Crandall, H. Ishii and P.-L. Lions, "User's guide to viscosity solutions of second order partial differential equations", Bull. Amer. Math. Soc. 27 (1992), 1–67, arXiv:math/9207212, Lemma 3.1 and Theorem 3.3.
