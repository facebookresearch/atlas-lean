# Dirichlet series of the twisted von Mangoldt function as a logarithmic derivative

Let $N$ be a natural number and $\chi$ a Dirichlet character modulo $N$ with complex values, let
$\Lambda$ be the von Mangoldt function, and let $L(s, \chi) = \sum_{n \ge 1} \chi(n)\, n^{-s}$ be the
$L$-series of $\chi$. Then for every complex number $s$ with $\operatorname{Re} s > 1$,

$$\sum_{n \ge 1} \chi(n)\, \Lambda(n)\, n^{-s} = -\frac{L'(s, \chi)}{L(s, \chi)},$$

where $L'(s, \chi)$ is the derivative of $L(s, \chi)$ with respect to $s$.

Both series converge absolutely for $\operatorname{Re} s > 1$, where $L(s, \chi) \ne 0$, and there
$-L'(s, \chi) = L(s, \chi) \sum_{n \ge 1} \chi(n)\, \Lambda(n)\, n^{-s}$, since on coefficients
$\chi(n) \log n$ is the Dirichlet convolution of $\chi$ with $\chi \Lambda$. For $N = 1$ the
character is trivial, $L(s, \chi)$ is the Riemann zeta function $\zeta(s)$ on $\operatorname{Re} s > 1$,
and the identity reads $\sum_{n \ge 1} \Lambda(n)\, n^{-s} = -\zeta'(s)/\zeta(s)$. For $N = 0$, where
$\chi(n) = 0$ for $n \ge 2$, both sides vanish.

## Sources

- Mathlib, `DirichletCharacter.LSeries_twist_vonMangoldt_eq` in `Mathlib.NumberTheory.LSeries.Dirichlet`,
  at the pinned commit
  <https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/NumberTheory/LSeries/Dirichlet.lean#L412-L413>.
- T. Tao, *254A, Notes 2: Complex-analytic multiplicative number theory* (2014),
  <https://terrytao.wordpress.com/2014/12/09/254a-notes-2-complex-analytic-multiplicative-number-theory/>:
  §4, "Dirichlet $L$-functions, Siegel's theorem, and the prime number theorem in arithmetic
  progressions", where $-L'(s, \chi)/L(s, \chi) = \sum_n \Lambda(n) \chi(n)/n^s$ on
  $\operatorname{Re} s > 1$ follows from $L \chi = \chi * (\Lambda \chi)$, with $L$ the logarithm.
