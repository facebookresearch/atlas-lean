# Cox–Ross–Rubinstein call price

In the $n$-period binomial model ($n \ge 0$) with initial stock price $S_0 > 0$, up and down
factors $u > R > d > 0$ and gross riskless return $R$ per period, let
$p = (R - d)/(u - d)$ be the [risk-neutral up probability](rn-prob.md) and let $p' = p u / R$.
For strike $K > 0$, take $a$ to be the least $j$ in $\{0,\ldots,n\}$ such that
$S_0 u^j d^{n-j} > K$, or $n+1$ if no such $j$ exists. On $0 \le j \le n$, the
terminal stock price is strictly above $K$ exactly when $a \le j$. The convention $a = n+1$
just records an empty tail: no stock prices are evaluated outside the feasible range, and a
terminal price equal to the strike is not counted.

The [backward-induction value](claim-value.md) of the European call with payoff $(S_n - K)^+$ is

$$
C_n = S_0\, \bar B(a; n, p') - \frac{K}{R^n}\, \bar B(a; n, p),
\qquad \bar B(a; n, q) = \sum_{j=a}^n \binom nj q^j (1 - q)^{n-j}.
$$

When $a=n+1$, both sums are empty and $C_n=0$.

## Sources

- J. C. Cox, S. A. Ross and M. Rubinstein, “Option pricing: a simplified approach”, *Journal of Financial Economics* 7(3):229–263, 1979. [DOI:10.1016/0304-405X(79)90015-1](https://doi.org/10.1016/0304-405X(79)90015-1)
