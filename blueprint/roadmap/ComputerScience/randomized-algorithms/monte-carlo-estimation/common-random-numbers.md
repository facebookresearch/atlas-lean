# Variance of common random numbers

Let $n \ge 1$. To estimate $E[f(X)] - E[g(X)]$ for square-integrable $f(X), g(X)$, the average of $f(X_i) - g(X_i)$ over $n$ i.i.d. $X_i$ has variance $(\operatorname{Var} f(X) + \operatorname{Var} g(X) - 2\operatorname{Cov}(f(X), g(X)))/n$, while differencing two independent averages of size $n$ has variance $(\operatorname{Var} f(X) + \operatorname{Var} g(X))/n$; common random numbers are at least as good exactly when $\operatorname{Cov}(f(X), g(X)) \ge 0$, for example when $f$ and $g$ are both nondecreasing functions of a single $U$.

Proof. Expand the variances. For the sign claim, with $V$ an independent copy of $U$ and $h, k$ monotone in the same direction, $(h(U) - h(V))(k(U) - k(V)) \ge 0$, and its expectation is $2\operatorname{Cov}(h(U), k(U))$.

## Sources

- A. B. Owen, *Monte Carlo Theory, Methods and Examples*, chapter 8 "Variance reduction", <https://artowen.su.domains/mc/>, §8.6 (formulas (8.19)–(8.20) and the variance comparison)
