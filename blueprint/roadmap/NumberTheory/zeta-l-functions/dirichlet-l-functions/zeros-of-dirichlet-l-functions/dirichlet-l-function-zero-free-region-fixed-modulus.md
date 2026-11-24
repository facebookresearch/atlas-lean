# Classical zero-free region for Dirichlet L-functions of a fixed modulus

There is a constant $c > 0$ with the following property. Fix a modulus $q \ge 1$, and call a
complex number $\rho \ne 1$ *exceptional for $q$* when

$$
\operatorname{Re} \rho > 1 - \frac{c}{\log\bigl(q (2 + |\operatorname{Im} \rho|)\bigr)}.
$$

If $L(\rho, \chi) = 0$ for a Dirichlet character $\chi$ modulo $q$ and an exceptional $\rho$,
then $\chi$ is real ($\chi^2$ is principal) and non-principal, $\rho$ is real and a simple zero of
$L(\cdot, \chi)$, and the pair $(\chi, \rho)$ is the only one for the modulus $q$: if
$L(\rho', \chi') = 0$ for a character $\chi'$ modulo $q$ and an exceptional $\rho'$, then
$\chi' = \chi$ and $\rho' = \rho$. Here $L(\cdot, \chi)$ is the meromorphic continuation of
$\sum_{n \ge 1} \chi(n) n^{-s}$, entire for non-principal $\chi$.

For the principal character this is the classical zero-free region of the Riemann zeta function,
since $L(s, \chi)$ then differs from $\zeta(s)$ by finitely many Euler factors without zeros in
$\operatorname{Re} s > 0$. For a non-principal character the proof combines the inequality
$3 + 4 \cos \theta + \cos 2\theta \ge 0$ with the approximate formula for $L'/L(\cdot, \chi)$ as a
sum over the zeros near a point, a consequence of Jensen's formula and the Borel–Carathéodory
theorem, and with its analogue for $\zeta'/\zeta$. That two distinct real characters modulo $q$
cannot both have an exceptional zero follows from Landau's theorem, through the inequality
$(1 + \chi(n))(1 + \chi'(n)) \ge 0$; a character and its primitive inducing character have the same
zeros in $\operatorname{Re} s > 0$.

## Proof depends on

- [Classical zero-free region for the Riemann zeta function](../../riemann-zeta/zero-free-regions-for-the-riemann-zeta-function/riemann-zeta-ne-zero-of-classical-zero-f.md)

## Sources

- T. Tao, *254A, Notes 2: Complex-analytic multiplicative number theory* (2014), <https://terrytao.wordpress.com/2014/12/09/254a-notes-2-complex-analytic-multiplicative-number-theory/>: Proposition 51 gives the zero-free region $\sigma > 1 - c / \log(q (2 + |t|))$ for each character $\chi$ modulo $q$ apart from at most one real zero, counted with multiplicity, which can occur only for a non-principal real $\chi$; its proof takes the principal character from Proposition 38 and treats the others with Exercise 45(ii) (the approximate formula for $L'/L$). Theorem 53 (Landau) and Exercise 52 (distinct characters modulo $q$ are induced by distinct primitive characters of conductor at most $q$, whose L-functions have the same zeros in $\operatorname{Re} s > 0$) show that at most one character modulo $q$ has such a zero. The fixed-modulus form is Proposition 6 of T. Tao, *254A, Notes 7: Linnik's theorem on primes in arithmetic progressions* (2015), <https://terrytao.wordpress.com/2015/02/22/254a-notes-7-linniks-theorem-on-primes-in-arithmetic-progressions/>.
