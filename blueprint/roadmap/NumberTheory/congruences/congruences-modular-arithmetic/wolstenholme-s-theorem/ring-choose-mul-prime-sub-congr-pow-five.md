# The congruence for $\binom{np}{kp}$ modulo $p^5$

Let $p \ge 11$ be a prime, let $k$ be a
natural number and let $n$ be an integer. For an integer $x$ and a natural number $r$ write
$\binom{x}{r} = x(x-1)\cdots(x-r+1)/r!$, and let $v_p$ be the $p$-adic valuation on
$\mathbb{Q}$. Put $C_{00} = -(k^2 - kn + 2n^2 - 15n + 35)/6$, $C_{21} = (n-4)(n-3)/2$,
$C_{31} = (n-2)(4-n)/3$, $C_{41} = (2k^2 - 2kn + n^2 - 3n + 4)/12$ and
$C_{42} = (n-k-1)(k-1)/12$, and let

$$
X = \binom{np}{kp} - \binom{n}{k} - \frac{k(n-k)}{2} \binom{n}{k} \Big(C_{00} +
C_{21} \binom{2p}{p} + C_{31} \binom{3p}{p} + C_{41} \binom{4p}{p} + C_{42} \binom{4p}{2p}\Big).
$$

Then either $X = 0$, or $\binom{n}{5} \ne 0$ and $v_p(X) \ge 5 + v_p\big(\binom{n}{5}\big)$; that
is, $X \equiv 0 \pmod{p^{5+v_p(\binom{n}{5})}}$, and $X = 0$ when $\binom{n}{5} = 0$.

The paper allows $n \in \mathbb{Z}_p$; only integers $n$ are covered here.

## Sources

- Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial Coefficients*, INTEGERS 26 (2026), Article A32, Proposition 4.
