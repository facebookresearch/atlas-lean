# The general congruence for $\binom{np}{kp}$

Let $p$ be a prime, let $m$ and $k$ be
natural numbers with $m + 1 < p$, and let $n$ be an integer. For an integer $x$ and a natural
number $r$ write $\binom{x}{r} = x(x-1)\cdots(x-r+1)/r!$, and let $v_p$ be the $p$-adic
valuation on $\mathbb{Q}$. For natural numbers $j$ and $l$ put

$$
c_j = \sum_{s=0}^{\min(j, k)} \binom{jp}{sp} \binom{n-j}{k-s}, \qquad
d_l = \binom{n}{l} \sum_{j=0}^{l} (-1)^{l-j} \binom{l}{j} c_j,
$$

and let $X = \binom{np}{kp} - \binom{n}{k} - (d_1 + \cdots + d_m)$. Then either $X = 0$, or
$\binom{n}{m+1} \ne 0$ and $v_p(X) \ge m + 1 + v_p\big(\binom{n}{m+1}\big)$. That is,
$\binom{np}{kp} - \binom{n}{k} \equiv d_1 + \cdots + d_m$ modulo $p^{m+1+v_p(\binom{n}{m+1})}$,
with equality when $\binom{n}{m+1} = 0$.

The paper allows $n \in \mathbb{Z}_p$; only integers $n$ are covered here.

## Sources

- Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial Coefficients*, INTEGERS 26 (2026), Article A32, Theorem 3 (`integers-2026-A32-thm-3`).
