# Antithetic sampling and common random numbers

(Antithetic sampling.) Let $n \ge 2$ be even, let $f(X)$ be square-integrable with variance $\sigma^2$, and let $\tilde X$ have the law of $X$. The average of $n/2$ i.i.d. pairs $(f(X_i) + f(\tilde X_i))/2$, using $n$ evaluations, has variance $(\sigma^2 + \operatorname{Cov}(f(X), f(\tilde X)))/n$, compared with $\sigma^2/n$ for $n$ independent evaluations; it is at most that exactly when $\operatorname{Cov}(f(X), f(\tilde X)) \le 0$. When $\sigma^2 > 0$ this is $\sigma^2(1 + \rho)/n$ with $\rho = \operatorname{Corr}(f(X), f(\tilde X))$, and the criterion is $\rho \le 0$; when $\sigma^2 = 0$ both variances are $0$. For $X = U$ uniform on $[0, 1]$, $\tilde X = 1 - U$ and $f$ monotone, the covariance is at most $0$.

(Common random numbers.) Let $n \ge 1$. To estimate $E[f(X)] - E[g(X)]$ for square-integrable $f(X), g(X)$, the average of $f(X_i) - g(X_i)$ over $n$ i.i.d. $X_i$ has variance $(\operatorname{Var} f(X) + \operatorname{Var} g(X) - 2\operatorname{Cov}(f(X), g(X)))/n$, while differencing two independent averages of size $n$ has variance $(\operatorname{Var} f(X) + \operatorname{Var} g(X))/n$; common random numbers are at least as good exactly when $\operatorname{Cov}(f(X), g(X)) \ge 0$, for example when $f$ and $g$ are both nondecreasing functions of a single $U$.

Proof. Expand the variances. For the sign claims, with $V$ an independent copy of $U$ and $h, k$ monotone in opposite (respectively the same) directions, $(h(U) - h(V))(k(U) - k(V)) \le 0$ (respectively $\ge 0$), and its expectation is $2\operatorname{Cov}(h(U), k(U))$.

## Sources

- A. B. Owen, *Monte Carlo Theory, Methods and Examples*, chapter 8 "Variance reduction", <https://artowen.su.domains/mc/>, §8.2 (formula (8.3)) and §8.6 (formulas (8.19)–(8.20) and the variance comparison)
