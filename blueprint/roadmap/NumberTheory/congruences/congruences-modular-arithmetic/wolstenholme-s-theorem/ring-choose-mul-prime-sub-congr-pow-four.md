# The congruence for $\binom{np}{kp}$ modulo $p^4$ via $\binom{2p}{p}$ and $\binom{3p}{p}$

Let $p \ge 7$ be a prime, let $k$ be a natural number and let $n$ be an integer. For an integer
$x$ and a natural number $r$ write $\binom{x}{r} = x(x-1)\cdots(x-r+1)/r!$, and let $v_p$ be
the $p$-adic valuation on $\mathbb{Q}$. Let

$$
X = \binom{np}{kp} - \binom{n}{k} - \frac{k(n-k)}{2} \binom{n}{k} \left((n - 4) +
(3 - n) \binom{2p}{p} + \frac{n - 2}{3} \binom{3p}{p}\right).
$$

Then either $X = 0$, or $\binom{n}{4} \ne 0$ and $v_p(X) \ge 4 + v_p\big(\binom{n}{4}\big)$; that
is, $X \equiv 0 \pmod{p^{4+v_p(\binom{n}{4})}}$, and $X = 0$ when $\binom{n}{4} = 0$.

The paper allows $n \in \mathbb{Z}_p$; only integers $n$ are covered here.

## Sources

- Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial Coefficients*, INTEGERS 26 (2026), Article A32, Proposition 3 (`integers-2026-A32-prop-3`).
