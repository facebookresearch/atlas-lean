# Frequency moment of a stream

For natural numbers $n$ and $k$ and a stream $l$ of elements of $\{0, \dots, n - 1\}$, with $m_i$ the number of occurrences of $i$ in $l$, the $k$-th frequency moment is the natural number

$$F_k = \sum_{i=0}^{n-1} m_i^k$$

(N. Alon, Y. Matias and M. Szegedy, *J. Comput. System Sci.* 58 (1999), Section 1). This agrees with the source for $k \ge 1$. For $k = 0$, with the convention $0^0 = 1$, it equals $n$, whereas the source's $F_0$ is the number of distinct elements of the stream.
