# Redundancy of the spillover representation

In the spillover representation with parameter $r$, the encoding is a bijection between $[X]$ and its image, the spill universe satisfies $r \le K \le 2r$ whenever $X > r$, and the redundancy satisfies

$$
M + \log_2 K - \log_2 X \le \frac{2}{r}.
$$

Hence $n$ independent payloads encoded with $r = n$ waste at most $3$ bits in total (at most $2$ from the spillover and at most $1$ from rounding) once their spill values are jointly encoded in $\lceil n \log_2 K \rceil$ bits.

## Proof sketch

Since $2^M \le X / r < 2^{M+1}$, we get $K = \lceil X/2^M \rceil \in [r, 2r]$ and $K 2^M < X + 2^M \le X (1 + 1/r)$, so $\log_2(K 2^M / X) \le \log_2(1 + 1/r) \le 2/r$ for $r \ge 1$.

## Depends on

- [Spillover representation of a bounded integer](spillover-representation.md)

## Sources

- M. Patrascu, "Succincter", Proceedings of the 49th IEEE Symposium on Foundations of Computer Science (FOCS), 2008.
- T. Li, J. Liang, H. Yu and R. Zhou, "Dynamic Dictionary with Subconstant Wasted Bits per Key", Proceedings of the 2024 ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 171-207, 2024; arXiv:2310.20536.
