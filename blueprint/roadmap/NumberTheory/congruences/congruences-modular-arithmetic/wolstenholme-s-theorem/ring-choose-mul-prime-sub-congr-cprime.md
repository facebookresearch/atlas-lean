# The congruence for $\binom{np}{kp}$ with symmetrized coefficients

Let $p$ be a prime,
let $m$ and $k$ be natural numbers with $m + 1 < p$, and let $n$ be an integer. For an integer
$x$ and a natural number $r$ write $\binom{x}{r} = x(x-1)\cdots(x-r+1)/r!$, for a rational
number $x$ write $(x)_r = x(x-1)\cdots(x-r+1)$ for the falling factorial, and let $v_p$ be the
$p$-adic valuation on $\mathbb{Q}$. Put

$$
C'_{00} = \left(\binom{m-k}{m} + \binom{k+m-n}{m} + (-1)^{m+1} \binom{n-1}{m} - 1\right)
\binom{n}{k}
$$

and, for $2 \le j \le m$ and $1 \le i \le \lfloor j/2 \rfloor$,

$$
C'_{ji} = \varepsilon_{ji} \, \frac{(n-k)_{j-i} \, (k)_i + (n-k)_i \, (k)_{j-i}}{j!}
\binom{m-n}{m-j} \binom{n}{k},
$$

where $\varepsilon_{ji} = 1/2$ if $j = 2i$ and $\varepsilon_{ji} = 1$ otherwise. Let

$$
X = \binom{np}{kp} - \binom{n}{k} - C'_{00} -
\sum_{j=2}^{m} \sum_{i=1}^{\lfloor j/2 \rfloor} C'_{ji} \binom{jp}{ip}.
$$

Then either $X = 0$, or $\binom{n}{m+1} \ne 0$ and
$v_p(X) \ge m + 1 + v_p\big(\binom{n}{m+1}\big)$. That is, $\binom{np}{kp} - \binom{n}{k}$ is
congruent to $C'_{00} + \sum_{j, i} C'_{ji} \binom{jp}{ip}$ modulo
$p^{m+1+v_p(\binom{n}{m+1})}$, and equal to it when $\binom{n}{m+1} = 0$.

The paper allows $n \in \mathbb{Z}_p$; only integers $n$ are covered here.

## Sources

- Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial Coefficients*, INTEGERS 26 (2026), Article A32, Theorem 4.
