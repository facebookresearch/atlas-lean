# Cox–Ross–Rubinstein prices converge to the Black–Scholes price

Let $C_n$ be the [Cox–Ross–Rubinstein call price](cox-ross-rubinstein-call-price.md) in the $n$-period binomial model with initial stock price $S_0 > 0$ and strike $K > 0$. With maturity $T > 0$, volatility $\sigma > 0$ and interest rate $r$, take $u_n = e^{\sigma\sqrt{T/n}}$, $d_n = 1/u_n$ and $R_n = e^{rT/n}$; then for $n$ large enough $u_n > R_n > d_n$, and $C_n$ converges as $n \to \infty$ to the [Black–Scholes call price](../../part-01/black-scholes-formula/black-scholes-call.md) $S_0 \Phi(d_1) - K e^{-rT} \Phi(d_2)$.

## Depends on

- [Cox–Ross–Rubinstein call price](cox-ross-rubinstein-call-price.md)
- [Black–Scholes price of a European call](../../part-01/black-scholes-formula/black-scholes-call.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- Convergence of binomial tail probabilities $\bar B(a_n; n, q_n)$ to Gaussian tails for success probabilities $q_n$ with $n q_n (1 - q_n) \to \infty$, for example from a central limit theorem for triangular arrays of Bernoulli variables (proof prerequisite)
- The asymptotics of $a_n$, $p_n$ and $p'_n$ under $u_n = e^{\sigma\sqrt{T/n}}$, $d_n = 1/u_n$ and $R_n = e^{rT/n}$ that identify the limits of the two tails with $\Phi(d_1)$ and $\Phi(d_2)$ (proof prerequisite)

## Sources

- J. C. Cox, S. A. Ross and M. Rubinstein, "Option pricing: a simplified approach", *Journal of Financial Economics* 7(3):229–263, 1979
