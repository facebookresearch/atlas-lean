# Linnik's theorem on the least prime in an arithmetic progression

There are absolute constants $C$ and $L$ such that for all integers $q \ge 1$ and $a$ coprime to
$q$ there is a prime $p \equiv a \pmod{q}$ with $p \le C q^L$.

The exponent $L$ is not specified here;
[Linnik's theorem with exponent 5.2 (Xylouris)](../../primes-primality/primality-tests-pseudoprimes/carmichael-numbers/exists-prime-mod-eq-le-rpow-five-point-t.md)
fixes $L = 5.2$.

The proof cited below deduces the theorem from an estimate for
$\psi(x; q, a) = \sum_{n \le x,\ n \equiv a \ (q)} \Lambda(n)$ when $x$ is a large power of
$q$, split according to whether some real character $\chi_1$ modulo $q$ has a real zero
$\beta = 1 - \varepsilon/\log q$ with $\varepsilon$ small. Without such a zero,
$\psi(x; q, a) = \frac{x}{\varphi(q)} \bigl(1 + O(e^{-c \log x / \log q}) + O(\log^2 q / q)\bigr)$;
with one, the main term becomes $\frac{x}{\varphi(q)} \bigl(1 - \chi_1(a) x^{\beta - 1}/\beta\bigr)$
and the first error term improves to $O(e^{-c (\log x / \log q) \log(1/\varepsilon)})$. The
estimate rests on the log-free truncated explicit formula, together with the zero-free region at a
fixed modulus, the log-free zero-density estimate and the Deuring–Heilbronn repulsion of zeros by
an exceptional zero.

## Proof depends on

- [Log-free truncated explicit formula for Dirichlet characters](../../zeta-l-functions/dirichlet-l-functions/log-free-truncated-explicit-formula.md)
- [Classical zero-free region for Dirichlet L-functions of a fixed modulus](../../zeta-l-functions/dirichlet-l-functions/dirichlet-l-function-zero-free-region-fixed-modulus.md)
- [Log-free zero-density estimate for Dirichlet L-functions](../../zeta-l-functions/dirichlet-l-functions/log-free-zero-density-estimate.md)
- [Deuring–Heilbronn repulsion of zeros by an exceptional zero](../../zeta-l-functions/dirichlet-l-functions/deuring-heilbronn-repulsion.md)

## Sources

- T. Tao, *254A, Notes 7: Linnik's theorem on primes in arithmetic progressions* (2015), <https://terrytao.wordpress.com/2015/02/22/254a-notes-7-linniks-theorem-on-primes-in-arithmetic-progressions/>: Theorem 1 (a primitive residue class $a \ (q)$ contains a prime $p \ll q^{O(1)}$), deduced from Theorem 2 by Exercise 3; Theorem 2 from Exercise 5 (the log-free truncated explicit formula), Proposition 6, Theorem 7 and Theorem 9, by Exercises 8 and 10. The notes follow H. Iwaniec and E. Kowalski, *Analytic Number Theory*, ch. 18; their proof of Theorem 9 has a gap that the author acknowledged in 2024 (see the Deuring–Heilbronn page).
- Provenance: L. Alpöge's Lean library proving the Riemann hypothesis and the generalized Riemann hypothesis for Dirichlet L-functions, released 2026-11-20 (<https://alpo.ge/remark.pdf>; source mirror <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>, no licence), contains Linnik's theorem with an unspecified exponent as `GlobalTheory.Published.Linnik`, proved as `UpperTheory.Lit.linnik`.
