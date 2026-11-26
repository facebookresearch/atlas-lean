# The AMS basic estimator of $F_k$

Let $l = (a_0, \dots, a_{m-1})$ be a stream of length $m$ over a set with decidable equality, $k$ a natural number and $p < m$ a position. With $r = \#\{q : p \le q < m,\ a_q = a_p\}$ the suffix count of $p$ (so $r \ge 1$), the basic estimator at $p$ is the real number

$$X = m\,\big(r^k - (r - 1)^k\big)$$

(N. Alon, Y. Matias and M. Szegedy, *J. Comput. System Sci.* 58 (1999), proof of Theorem 2.1). For $k = 0$ it is $0$.

## Background

- [Suffix count of a stream position](suffix-count.md): the quantity $r$.
