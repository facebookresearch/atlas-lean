# Cox–Ross–Rubinstein call price

In the $n$-period binomial model with initial stock price $S_0 > 0$, up and down factors $u > R > d > 0$ and gross riskless return $R$ per period, let $p = (R - d)/(u - d)$ be the [risk-neutral up probability](rn-prob.md) and $p' = p u / R$. For strike $K > 0$, let $a$ be the least integer $j \ge 0$ with $S_0 u^j d^{n-j} > K$. The [backward-induction value](claim-value.md) of the European call with payoff $(S_n - K)^+$ is

$$C_n = S_0\, \bar B(a; n, p') - K R^{-n}\, \bar B(a; n, p), \qquad \bar B(a; n, q) = \sum_{j=a}^n \binom nj q^j (1 - q)^{n-j},$$

and $C_n = 0$ when $a > n$.

## Depends on

- [Risk-neutral up probability of the binomial model](rn-prob.md)
- [Backward-induction value of a path-dependent claim](claim-value.md)

## Sources

- J. C. Cox, S. A. Ross and M. Rubinstein, "Option pricing: a simplified approach", *Journal of Financial Economics* 7(3):229–263, 1979
