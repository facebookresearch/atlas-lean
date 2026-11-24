# The AMS estimator is unbiased for $F_k$

Let $\iota$ be a finite set of $n$ symbols and $l = (a_0, \dots, a_{m-1})$ a stream of $m$ elements of $\iota$; write $m_i$ for the number of occurrences of $i$ in $l$ and $F_k = \sum_{i \in \iota} m_i^k$. For a position $p < m$, let $r_p = \#\{q : p \le q < m,\ a_q = a_p\}$ be the number of occurrences of $a_p$ from position $p$ on, and $X_p = m\,(r_p^k - (r_p - 1)^k)$ the basic estimator. If $k \ge 1$, then

$$\frac{1}{m} \sum_{p < m} X_p = F_k,$$

with the convention $1/0 = 0$, so that both sides are $0$ for the empty stream. Thus, for a nonempty stream and a uniformly random position $p$, $\mathbb{E}[X_p] = F_k$ (N. Alon, Y. Matias and M. Szegedy, *J. Comput. System Sci.* 58 (1999), proof of Theorem 2.1).

The sum telescopes: the positions holding symbol $i$ have $r_p = 1, \dots, m_i$, and $\sum_{r=1}^{m_i} (r^k - (r-1)^k) = m_i^k$. The hypothesis $k \ge 1$ is needed: for $k = 0$ the estimator is identically $0$.

## Informally uses

- [Suffix counts enumerate each multiplicity once](sum-suffix-count.md): regroups the sum over positions by symbol.
