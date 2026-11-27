# Second moment of the AMS estimator against $F_k^2$

Let $\iota$ be a finite set of $n$ symbols and $l = (a_0, \dots, a_{m-1})$ a stream of $m$ elements of $\iota$; write $m_i$ for the number of occurrences of $i$ in $l$ and $F_k = \sum_{i \in \iota} m_i^k$. For a position $p < m$, let $r_p = \#\{q : p \le q < m,\ a_q = a_p\}$ be the number of occurrences of $a_p$ from position $p$ on, and $X_p = m\,(r_p^k - (r_p - 1)^k)$ the basic estimator. If $k \ge 1$, then

$$\frac{1}{m} \sum_{p < m} X_p^2 \le k\, n^{1 - 1/k} F_k^2,$$

with the convention $1/0 = 0$ for the empty stream, whose average is $0$. Consequently, since a variance is at most the second moment, for a nonempty stream and a positive integer $s_1$, the mean $Y$ of $s_1$ independent copies of $X_p$, each with a uniformly random position $p$, has $\operatorname{Var}(Y) \le k n^{1-1/k} F_k^2 / s_1$ (N. Alon, Y. Matias and M. Szegedy, *J. Comput. System Sci.* 58 (1999), proof of Theorem 2.1).

## Informally uses

- [Second moment of the AMS estimator](average-basic-estimator-sq-le.md): the bound $k F_1 F_{2k-1}$.
- [The moment inequality](sum-mul-sum-le-rpow.md): $F_1 F_{2k-1} \le n^{1-1/k} F_k^2$.

## Background

- [Variance bound for the AMS sketch](variance-sketch-sq-le.md): for $k = 2$ the sketch of Theorem 2.2 replaces the factor $2 n^{1/2}$ by $2$, which is why $F_2$ needs only logarithmic space.
