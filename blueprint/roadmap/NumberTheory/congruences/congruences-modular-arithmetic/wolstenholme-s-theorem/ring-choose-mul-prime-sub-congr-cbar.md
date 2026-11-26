# Congruence for $\binom{np}{kp}$ with the coefficients $\bar C_{ji}$

Let $p$ be a prime,
let $m$ and $k$ be natural numbers with $m + 1 < p$, and let $n$ be an integer. For an integer
$x$ and a natural number $r$ write $\binom{x}{r} = x(x-1)\cdots(x-r+1)/r!$, and set
$\binom{x}{r} = 0$ for negative $r$. Let

$$\bar C_{00} = \left( \binom{m-k}{m} + \binom{k+m-n}{m} + (-1)^{m+1} \binom{n-1}{m} - 1 \right)
\binom{n}{k},$$

let $\bar C_{ji} = \binom{n}{j} \binom{m-n}{m-j} \binom{n-j}{k-i}$, and let

$$X = \binom{np}{kp} - \binom{n}{k} - \bar C_{00} -
\sum_{1 \le i < j \le m} \bar C_{ji} \binom{jp}{ip}.$$

Then either $X = 0$, or $\binom{n}{m+1} \ne 0$ and
$v_p(X) \ge m + 1 + v_p\big(\binom{n}{m+1}\big)$, where $v_p$ is the $p$-adic valuation on
$\mathbb{Q}$. With $v_p(0) = \infty$ this says $X \equiv 0 \pmod{p^{m+1+v_p(\binom{n}{m+1})}}$.

## Sources

- Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial Coefficients*, INTEGERS 26 (2026), Article A32, Lemma 4.
