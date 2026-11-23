# The congruence for $\binom{np}{kp}$ modulo $p^7$

Let $p \ge 11$ be a prime, let $k$ be a
natural number and let $n$ be an integer. For an integer $x$ and a natural number $r$ write
$\binom{x}{r} = x(x-1)\cdots(x-r+1)/r!$, and let $v_p$ be the $p$-adic valuation on
$\mathbb{Q}$. Put

$$
C_{00} = -\frac{1}{360} \big(2k^4 - 4k^3 n + 11k^2 n^2 - 9k n^3 + 6n^4 - 105k^2 n + 105k n^2 -
105n^3 + 350k^2 - 350kn + 700n^2 - 2205n + 3248\big),
$$

$C_{21} = (6-n)(5-n)(4-n)(3-n)/24$, $C_{31} = (n-2)(6-n)(5-n)(4-n)/18$,
$C_{41} = (6-n)(5-n)(2k^2 - 2kn + n^2 - 3n + 4)/24$,
$C_{42} = (n-k-1)(k-1)(6-n)(5-n)/24$,
$C_{51} = (4-n)(n-6)(3k^2 - 3kn + n^2 - 2n + 3)/60$,
$C_{52} = (k+1-n)(k-1)(n-4)(n-6)/60$,

$$
C_{61} = \frac{1}{360} \big(2k^4 - 4k^3 n + 6k^2 n^2 - 4k n^3 + n^4 - 30k^2 n + 30k n^2 -
10n^3 + 70k^2 - 70kn + 35n^2 - 50n + 48\big),
$$

$C_{62} = (n-k-1)(k-1)(2k^2 - 2kn + n^2 - 5n + 12)/360$ and
$C_{63} = (n-k-1)(n-k-2)(k-1)(k-2)/360$, and let

$$
X = \binom{np}{kp} - \binom{n}{k} - \frac{k(n-k)}{2} \binom{n}{k} \Big(C_{00} +
\sum_{j=2}^{6} \sum_{i=1}^{\lfloor j/2 \rfloor} C_{ji} \binom{jp}{ip}\Big).
$$

Then either $X = 0$, or $\binom{n}{7} \ne 0$ and $v_p(X) \ge 7 + v_p\big(\binom{n}{7}\big)$; that
is, $X \equiv 0 \pmod{p^{7+v_p(\binom{n}{7})}}$, and $X = 0$ when $\binom{n}{7} = 0$.

Two coefficients differ from the printed paper and follow its Definition 1 and Theorem 4:
$C_{00}$ has the prefactor $-1/360$ (printed $-1/720$), and $C_{63}$ has the factor
$(n-k-1)(n-k-2)$ (printed $(k-n-1)(k-n-2)$). With the printed values the congruence fails
already modulo $p$, for instance at $p = 11$, $n = 7$, $k = 1$. The paper allows
$n \in \mathbb{Z}_p$; only integers $n$ are covered here.

## Sources

- Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial Coefficients*, INTEGERS 26 (2026), Article A32, Proposition 6.
