# Variance of antithetic sampling

Let $n \ge 2$ be even, let $f(X)$ be square-integrable with variance $\sigma^2$, and let $\tilde X$ have the law of $X$. The average of $n/2$ i.i.d. pairs $(f(X_i) + f(\tilde X_i))/2$, using $n$ evaluations, has variance $(\sigma^2 + \operatorname{Cov}(f(X), f(\tilde X)))/n$, compared with $\sigma^2/n$ for $n$ independent evaluations; it is at most that exactly when $\operatorname{Cov}(f(X), f(\tilde X)) \le 0$. When $\sigma^2 > 0$ this is $\sigma^2(1 + \rho)/n$ with $\rho = \operatorname{Corr}(f(X), f(\tilde X))$, and the criterion is $\rho \le 0$; when $\sigma^2 = 0$ both variances are $0$. For $X = U$ uniform on $[0, 1]$, $\tilde X = 1 - U$ and $f$ monotone, the covariance is at most $0$.

Proof. Expand the variances. For the sign claim, with $V$ an independent copy of $U$ and $h, k$ monotone in opposite directions, $(h(U) - h(V))(k(U) - k(V)) \le 0$, and its expectation is $2\operatorname{Cov}(h(U), k(U))$; take $h = f$ and $k(u) = f(1 - u)$.

## Sources

- A. B. Owen, *Monte Carlo Theory, Methods and Examples*, chapter 8 "Variance reduction", <https://artowen.su.domains/mc/>, §8.2 (formula (8.3))
