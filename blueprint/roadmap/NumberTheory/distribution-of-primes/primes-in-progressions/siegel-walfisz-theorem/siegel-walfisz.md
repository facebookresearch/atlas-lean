# Siegel–Walfisz theorem for Chebyshev's function in residue classes

For every real $N > 0$
there are real constants $c > 0$, $C > 0$ and $X_0 > 1$ such that for every real $x \ge X_0$, every
positive integer $q$ with $q \le (\log x)^N$ and every unit $a$ of $\mathbb{Z}/q\mathbb{Z}$,

$$\left|\psi(x; q, a) - \frac{x}{\varphi(q)}\right| \le C x \exp\left(-c \sqrt{\log x}\right),$$

where $\psi(x; q, a)$ is Chebyshev's function in the residue class $a$ modulo $q$ and $\varphi$ is
Euler's totient function.

The constants may depend on $N$, but not on $x$, $q$, or $a$.

## Informally uses

- [Truncated explicit formula for $\psi(x, \chi)$](../../../zeta-l-functions/dirichlet-l-functions/truncated-explicit-formula.md), for $\psi(x, \chi)$ with $\chi$ modulo $q$, principal or not
- [Classical zero-free region for Dirichlet L-functions of a fixed modulus](../../../zeta-l-functions/dirichlet-l-functions/dirichlet-l-function-zero-free-region-fixed-modulus.md), for the zeros other than a possible exceptional real zero
- [Siegel's theorem](../../../zeta-l-functions/dirichlet-l-functions/siegel-theorem.md), for the exceptional real zero $\beta$, through $\beta < 1 - c(\varepsilon) q^{-\varepsilon}$

## Sources

- P. Holdridge, *Random Diophantine Equations in the Primes*, arXiv:2305.06306v2, Theorem 4.2, citing H. Davenport, *Multiplicative Number Theory*, 2nd ed., revised by H. L. Montgomery, Springer, 1980, Chapter 22.
- Proof: J. Teräväinen, "The Siegel-Walfisz theorem", *Joni's Math Notes*, 30 January 2015,
  <https://jonismathnotes.blogspot.com/2015/01/the-siegel-walfisz-theorem.html>, following Davenport:
  Theorem 1 (explicit formula for $\psi(x, \chi)$), the theorem that zeros with
  $\sigma > 1 - c/\log q$ come only from a real zero of a real non-principal character, at most one
  for each modulus, Theorem 6 (Siegel: (i) $L(1, \chi) > C(\varepsilon) q^{-\varepsilon}$, and (ii),
  derived from (i) by a bound for $L'(\sigma, \chi)$, no zero with $\sigma > 1 - C(\varepsilon) q^{-\varepsilon}$)
  and Theorem 7 (Siegel–Walfisz), whose proof combines them for each character and uses the
  explicit formula for the principal character with the zero-free region of $\zeta$.
- T. Tao, *254A, Notes 2: Complex-analytic multiplicative number theory*, 9 December 2014,
  <https://terrytao.wordpress.com/2014/12/09/254a-notes-2-complex-analytic-multiplicative-number-theory/>:
  Exercise 64 (the Siegel–Walfisz theorem, "use Exercise 55 (iii) together with Siegel's theorem to
  handle the exceptional zero"), with Exercise 55 (the prime number theorem in arithmetic
  progressions with an exceptional-zero term), Exercise 45 (iv) and Proposition 51.
