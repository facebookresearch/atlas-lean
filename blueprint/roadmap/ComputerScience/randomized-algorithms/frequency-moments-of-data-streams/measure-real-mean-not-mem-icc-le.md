# Chebyshev step for one mean of AMS estimators

Let $\mu$ be a probability measure, $\iota$ a finite set, $s_1$ a natural number, and for each $k < s_1$ let $(\varepsilon_{k,i})_{i \in \iota}$ be measurable random variables with values in $\{-1, 1\}$, mean $0$ and [four-wise independent](four-wise-independent.md), the $s_1$ families $(\varepsilon_{k,i})_i$ being mutually independent. Let $(m_i)_{i \in \iota}$ be real weights and $F = \sum_i m_i^2$. If $\lambda > 0$ and $s_1 \ge 16/\lambda^2$, then the mean

$$Y = \frac{1}{s_1} \sum_{k < s_1} \Big(\sum_i m_i \varepsilon_{k,i}\Big)^2$$

satisfies $\Pr\big[Y \notin [F - \lambda F, F + \lambda F]\big] \le 1/8$.

When $F = 0$ all weights vanish, $Y = 0$ and the statement is trivial. Otherwise each square has mean $F$ and variance at most $2F^2$, so Chebyshev's inequality bounds the probability by $2F^2/(s_1 \lambda^2 F^2) = 2/(s_1 \lambda^2) \le 1/8$. Alon, Matias and Szegedy take exactly $s_1 = 16/\lambda^2$, for which the bound equals $1/8$ (N. Alon, Y. Matias and M. Szegedy, *J. Comput. System Sci.* 58 (1999), proof of Theorem 2.2).

## Informally uses

- [Variance bound for the AMS estimator](variance-sq-weighted-sum-le.md): $\operatorname{Var}(Z^2) \le 2F^2$ for each copy.
- [Unbiasedness of the AMS estimator](integral-sq-weighted-sum.md): each copy has mean $F$.
