# The congruence for $\binom{np}{kp}$ modulo $p^4$ via $\binom{2p}{p}$ alone

Let
$p \ge 7$ be a prime, let $k$ be a natural number and let $n$ be an integer. For an integer $x$
and a natural number $r$ write $\binom{x}{r} = x(x-1)\cdots(x-r+1)/r!$, and let $v_p$ be the
$p$-adic valuation on $\mathbb{Q}$, with the convention $v_p(0) = 0$. Let

$$
X = \binom{np}{kp} - \binom{n}{k} - \frac{nk(n-k)}{4} \binom{n}{k} \left(\binom{2p}{p} - 2\right).
$$

Then either $X = 0$ or $v_p(X) \ge 4 + v_p\big(\binom{n}{4}\big)$. In particular, when
$\binom{n}{4} = 0$, that is $n \in \{0, 1, 2, 3\}$, the conclusion is only that $X = 0$ or
$v_p(X) \ge 4$.

Equality cannot be demanded when $\binom{n}{4} = 0$: for $p = 7$, $n = 3$ and $k = 1$ one has
$X = 100842 = 6 \cdot 7^5$. The paper allows $n \in \mathbb{Z}_p$; only integers $n$ are covered
here.

## Sources

- Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial Coefficients*, INTEGERS 26 (2026), Article A32, Theorem 6 (`integers-2026-A32-thm-6`).
