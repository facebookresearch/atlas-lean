# Cox–Ross–Rubinstein call price and convergence to Black–Scholes

In the $n$-period binomial model with initial stock price $S_0 > 0$, up and down factors $u > R > d > 0$ and gross riskless return $R$ per period, let $p = (R - d)/(u - d)$ be the [risk-neutral up probability](rn-prob.md) and $p' = p u / R$. For strike $K > 0$, let $a$ be the least integer $j \ge 0$ with $S_0 u^j d^{n-j} > K$. The [backward-induction value](claim-value.md) of the European call with payoff $(S_n - K)^+$ is

$$C_n = S_0\, \bar B(a; n, p') - K R^{-n}\, \bar B(a; n, p), \qquad \bar B(a; n, q) = \sum_{j=a}^n \binom nj q^j (1 - q)^{n-j},$$

and $C_n = 0$ when $a > n$. With maturity $T > 0$, volatility $\sigma > 0$ and interest rate $r$, take $u_n = e^{\sigma\sqrt{T/n}}$, $d_n = 1/u_n$ and $R_n = e^{rT/n}$; then for $n$ large enough $u_n > R_n > d_n$, and $C_n$ converges as $n \to \infty$ to the [Black–Scholes call price](../../part-01/black-scholes-formula/black-scholes-call.md) $S_0 \Phi(d_1) - K e^{-rT} \Phi(d_2)$.

## Depends on

- [Risk-neutral up probability of the binomial model](rn-prob.md)
- [Backward-induction value of a path-dependent claim](claim-value.md)
- [Black–Scholes price of a European call](../../part-01/black-scholes-formula/black-scholes-call.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- Convergence of binomial tail probabilities $\bar B(a_n; n, q_n)$ to Gaussian tails for success probabilities $q_n$ with $n q_n (1 - q_n) \to \infty$, for example from a central limit theorem for triangular arrays of Bernoulli variables (proof prerequisite)
- The asymptotics of $a_n$, $p_n$ and $p'_n$ under $u_n = e^{\sigma\sqrt{T/n}}$, $d_n = 1/u_n$ and $R_n = e^{rT/n}$ that identify the limits of the two tails with $\Phi(d_1)$ and $\Phi(d_2)$ (proof prerequisite)

## Sources

- J. C. Cox, S. A. Ross and M. Rubinstein, "Option pricing: a simplified approach", *Journal of Financial Economics* 7(3):229–263, 1979
