# The congruence for $\binom{np}{kp}$ modulo $p^6$

Let $p \ge 11$ be a prime, let $k$ be a
natural number and let $n$ be an integer. For an integer $x$ and a natural number $r$ write
$\binom{x}{r} = x(x-1)\cdots(x-r+1)/r!$, and let $v_p$ be the $p$-adic valuation on
$\mathbb{Q}$. Put $C_{00} = (n-6)(n^2 - nk - 6n + k^2 + 15)/12$,
$C_{21} = (5-n)(4-n)(3-n)/6$, $C_{31} = (n-2)(n-5)(n-4)/6$,
$C_{41} = (2k^2 - 2kn + n^2 - 3n + 4)(5-n)/12$, $C_{42} = (k+1-n)(k-1)(n-5)/12$,
$C_{51} = (n-4)(3k^2 - 3kn + n^2 - 2n + 3)/60$ and $C_{52} = (n-k-1)(k-1)(n-4)/60$, and let

$$
X = \binom{np}{kp} - \binom{n}{k} - \frac{k(n-k)}{2} \binom{n}{k} \Big(C_{00} +
\sum_{j=2}^{5} \sum_{i=1}^{\lfloor j/2 \rfloor} C_{ji} \binom{jp}{ip}\Big).
$$

Then either $X = 0$, or $\binom{n}{6} \ne 0$ and $v_p(X) \ge 6 + v_p\big(\binom{n}{6}\big)$; that
is, $X \equiv 0 \pmod{p^{6+v_p(\binom{n}{6})}}$, and $X = 0$ when $\binom{n}{6} = 0$.

The paper allows $n \in \mathbb{Z}_p$; only integers $n$ are covered here.

## Sources

- Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial Coefficients*, INTEGERS 26 (2026), Article A32, Proposition 5 (`integers-2026-A32-prop-5`).
