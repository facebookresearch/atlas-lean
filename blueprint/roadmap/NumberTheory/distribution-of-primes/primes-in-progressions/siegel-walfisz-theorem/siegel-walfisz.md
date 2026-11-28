# Siegel–Walfisz theorem for Chebyshev's function in residue classes

For every real $N > 0$
there are real constants $c > 0$, $C > 0$ and $X_0 > 1$ such that for every real $x \ge X_0$, every
positive integer $q$ with $q \le (\log x)^N$ and every unit $a$ of $\mathbb{Z}/q\mathbb{Z}$,

$$\left|\psi(x; q, a) - \frac{x}{\varphi(q)}\right| \le C x \exp\left(-c \sqrt{\log x}\right),$$

where $\psi(x; q, a)$ is Chebyshev's function in the residue class $a$ modulo $q$ and $\varphi$ is
Euler's totient function.

The constants may depend on $N$, but not on $x$, $q$, or $a$.

## Informally uses

- [Truncated explicit formula for $\psi(x, \chi)$](../../../zeta-l-functions/dirichlet-l-functions/truncated-explicit-formula.md), for $\psi(x, \chi)$ with $\chi$ non-principal, and in Tao's route also for the principal character
- [Classical zero-free region for Dirichlet L-functions of a fixed modulus](../../../zeta-l-functions/dirichlet-l-functions/zeros-of-dirichlet-l-functions/dirichlet-l-function-zero-free-region-fixed-modulus.md), for the zeros of height at most $T$ other than a possible exceptional real zero, at most one for each modulus
- [Siegel's theorem](../../../zeta-l-functions/dirichlet-l-functions/zeros-of-dirichlet-l-functions/siegel-theorem.md), for the exceptional real zero $\beta$ of a real character, through $\beta < 1 - c(\varepsilon) q^{-\varepsilon}$
- [Prime number theorem with error term for Chebyshev's $\theta$](../../prime-number-theorem/error-term-in-the-prime-number-theorem/prime-number-theorem-chebyshev-theta-err.md), for the principal character in Teräväinen's proof: $\psi(x, \chi_0)$ differs from $\theta(x)$ only by terms from the prime powers $p^k \le x$ with $k \ge 2$ and from the primes dividing $q$

## Sources

- P. Holdridge, *Random Diophantine Equations in the Primes*, arXiv:2305.06306v2, Theorem 4.2, citing H. Davenport, *Multiplicative Number Theory*, 2nd ed., revised by H. L. Montgomery, Springer, 1980, Chapter 22.
- Proof: J. Teräväinen, "The Siegel-Walfisz theorem", *Joni's Math Notes*, 30 January 2015,
  <https://jonismathnotes.blogspot.com/2015/01/the-siegel-walfisz-theorem.html>, following Davenport:
  Theorem 1 (the explicit formula for $\psi(x, \chi)$, $\chi$ non-principal, beside the formula for
  $\psi(x)$), the theorems on Landau–Siegel zeros (a zero of $L(s, \chi)$, $\chi$ modulo $q$, with
  $\beta > 1 - c/\log(q(2 + |\gamma|))$ is a real zero of a real non-principal character, and there is at
  most one for each modulus), Theorem 6 (Siegel: (i) $L(1, \chi) > C(\varepsilon) q^{-\varepsilon}$ for
  real primitive $\chi$, and (ii), derived from (i) by a bound for $L'(\sigma, \chi)$, no real zero with
  $\sigma > 1 - C(\varepsilon) q^{-\varepsilon}$), and Theorem 7 (Siegel–Walfisz). Its proof bounds
  $\psi(x, \chi)$ for each non-principal $\chi$ with the explicit formula, the zero-free region
  $\beta \le 1 - c/\log(q(T + 2))$ for the zeros with $|\gamma| \le T$ other than the exceptional one,
  and (ii) for the exceptional real zero; for the principal character it uses the prime number theorem
  with error term, $\psi(x, \chi_0) - x \ll x \exp(-\sqrt{\log x})$, since $\psi(x, \chi_0)$ differs from
  $\psi(x)$ only by the prime powers of the primes dividing $q$.
- T. Tao, *254A, Notes 2: Complex-analytic multiplicative number theory*, 9 December 2014,
  <https://terrytao.wordpress.com/2014/12/09/254a-notes-2-complex-analytic-multiplicative-number-theory/>:
  Exercise 64 (the Siegel–Walfisz theorem, "use Exercise 55 (iii) together with Siegel's theorem to
  handle the exceptional zero"), with Exercise 55 (the prime number theorem in arithmetic
  progressions with an exceptional-zero term, for the principal and the non-principal characters,
  with at most one exceptional character for each modulus by Page's theorem), which follows from
  Exercise 45 (iv) (the truncated explicit formula) and Proposition 51 (the classical zero-free
  region).
