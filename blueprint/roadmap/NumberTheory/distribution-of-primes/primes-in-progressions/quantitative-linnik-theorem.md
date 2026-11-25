# Quantitative Linnik theorem for primes in arithmetic progressions

For a modulus $q \ge 2$ and an integer $a$ coprime to $q$, let
$\psi(x; q, a) = \sum_{n \le x,\ n \equiv a \ (q)} \Lambda(n)$, where $\Lambda$ is the von Mangoldt
function. There is an absolute constant $\varepsilon_0 > 0$, and for every $\delta > 0$ there are
constants $C, c > 0$, such that for all such $q$ and $a$ and every real $x \ge q^{C}$ the following
hold, with implied constants depending only on $\delta$; all constants are effective.

- If every real zero $\beta$ of an L-function $L(\cdot, \chi)$ of a real Dirichlet character $\chi$
  modulo $q$ satisfies $1 - \beta \ge \delta / \log q$, then

$$
\psi(x; q, a) = \frac{x}{\varphi(q)} \Bigl( 1 + O\bigl( e^{-c \log x / \log q} \bigr) + O\Bigl( \frac{\log^2 q}{q} \Bigr) \Bigr).
$$

- If $L(\beta, \chi_1) = 0$ for a real character $\chi_1$ modulo $q$ and $\beta = 1 - \varepsilon / \log q$
  with $0 < \varepsilon \le \varepsilon_0$, then

$$
\psi(x; q, a) = \frac{x}{\varphi(q)} \Bigl( 1 - \chi_1(a) \frac{x^{\beta - 1}}{\beta} + O\bigl( e^{-c (\log x / \log q) \log(1/\varepsilon)} \bigr) + O\Bigl( \frac{\log^2 q}{q} \Bigr) \Bigr).
$$

The improved error term in the second case compensates for the possible loss in the main term. The
estimate gives $\psi(x; q, a) \gg x / \varphi(q)$, respectively $\gg \varepsilon x / \varphi(q)$, when $x$ is
a large enough power of $q$, and with it Linnik's theorem: every primitive residue class modulo $q$
contains a prime $p \le C' q^{L}$ for absolute constants $C'$ and $L$;
[Linnik's theorem with exponent 5.2 (Xylouris)](../../primes-primality/primality-tests-pseudoprimes/carmichael-numbers/exists-prime-mod-eq-le-rpow-five-point-t.md)
fixes $L = 5.2$.

The proof rests on the log-free truncated explicit formula, together with the zero-free region at a
fixed modulus, the log-free zero-density estimate and the Deuring–Heilbronn repulsion of zeros by an
exceptional zero.

## Proof depends on

- [Log-free truncated explicit formula for Dirichlet characters](../../zeta-l-functions/dirichlet-l-functions/log-free-truncated-explicit-formula.md)
- [Classical zero-free region for Dirichlet L-functions of a fixed modulus](../../zeta-l-functions/dirichlet-l-functions/zeros-of-dirichlet-l-functions/dirichlet-l-function-zero-free-region-fixed-modulus.md)
- [Log-free zero-density estimate for Dirichlet L-functions](../../zeta-l-functions/dirichlet-l-functions/zeros-of-dirichlet-l-functions/log-free-zero-density-estimate.md)
- [Deuring–Heilbronn repulsion of zeros by an exceptional zero](../../zeta-l-functions/dirichlet-l-functions/zeros-of-dirichlet-l-functions/deuring-heilbronn-repulsion.md)

## Sources

- T. Tao, *254A, Notes 7: Linnik's theorem on primes in arithmetic progressions* (2015), <https://terrytao.wordpress.com/2015/02/22/254a-notes-7-linniks-theorem-on-primes-in-arithmetic-progressions/>: Theorem 2 (quantitative Linnik theorem, "a special case of a more powerful theorem of Gallagher", with the hypothesis $1 - \beta \gg 1/\log q$ in its first case and effective implied constants), proved from Exercise 5 (the log-free truncated explicit formula), Proposition 6, Theorem 7 and Theorem 9 by Exercises 8 and 10; Exercise 3 deduces Theorem 1 (Linnik's theorem) from it. The notes follow H. Iwaniec and E. Kowalski, *Analytic Number Theory*, ch. 18; their proof of Theorem 9 has a gap that the author acknowledged in 2024 (see the Deuring–Heilbronn page).
- Provenance: L. Alpöge's Lean library proving the Riemann hypothesis and the generalized Riemann hypothesis for Dirichlet L-functions, released 2026-11-20 (<https://alpo.ge/remark.pdf>; source mirror <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>), contains Linnik's theorem with an unspecified exponent, a consequence of this estimate, as `GlobalTheory.Published.Linnik`, proved as `UpperTheory.Lit.linnik`.
