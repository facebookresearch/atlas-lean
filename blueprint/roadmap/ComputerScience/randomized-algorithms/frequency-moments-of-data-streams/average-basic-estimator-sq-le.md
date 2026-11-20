# Second moment of the AMS estimator

Let $\iota$ be a finite set of $n$ symbols and $l = (a_0, \dots, a_{m-1})$ a stream of $m$ elements of $\iota$; write $m_i$ for the number of occurrences of $i$ in $l$ and $F_k = \sum_{i \in \iota} m_i^k$. For a position $p < m$, let $r_p = \#\{q : p \le q < m,\ a_q = a_p\}$ be the number of occurrences of $a_p$ from position $p$ on, and $X_p = m\,(r_p^k - (r_p - 1)^k)$ the basic estimator. If $k \ge 1$, then

$$\frac{1}{m} \sum_{p < m} X_p^2 \le k\, m \sum_{i \in \iota} m_i^{2k-1} = k\, F_1 F_{2k-1},$$

with the convention $1/0 = 0$ for the empty stream (N. Alon, Y. Matias and M. Szegedy, *J. Comput. System Sci.* 58 (1999), proof of Theorem 2.1, using $a^k - b^k \le (a - b)\, k\, a^{k-1}$ for $0 \le b \le a$).

## Informally uses

- [Suffix counts enumerate each multiplicity once](sum-suffix-count.md): regroups the sum over positions by symbol.
