# Weak prime number theorem in arithmetic progressions

Let $q$ and $a$ be natural numbers with
$a < q$ and $\gcd(a, q) = 1$, let $\Lambda$ be the von Mangoldt function and let $\varphi$ be
Euler's totient function. Then, as $N \to \infty$ through the natural numbers,

$$
\frac{1}{N} \sum_{\substack{0 \le n < N \\ n \equiv a \pmod{q}}} \Lambda(n) \to
\frac{1}{\varphi(q)}.
$$

## Sources

- the proved theorem `PrimeNumberTheoremAnd.WeakPNT_AP` in [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd), and its use in [arXiv:2608.24035](https://arxiv.org/abs/2608.24035). Lean preserves the source's natural representative and half-open `Finset.range` normalization, while omitting the redundant assumption `1 ≤ q`, which follows from `a < q`.
