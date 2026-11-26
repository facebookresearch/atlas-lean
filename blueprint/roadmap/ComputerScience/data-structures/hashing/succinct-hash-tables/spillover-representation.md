# Spillover representation of a bounded integer

Let $X \ge 1$ and $r \ge 1$. Set $M = 0$ if $X \le r$ and $M = \lfloor \log_2(X / r) \rfloor$ otherwise, and $K = \lceil X / 2^M \rceil$. The *spillover representation* of $x \in [X]$ is the pair $(\lfloor x / 2^M \rfloor, x \bmod 2^M) \in [K] \times [2^M]$: an $M$-bit word stored in memory together with a *spill* value in the small universe $[K]$ that is passed to metadata. Decoding is $x = k 2^M + m$.

## Sources

- M. Patrascu, "Succincter", Proceedings of the 49th IEEE Symposium on Foundations of Computer Science (FOCS), 2008.
- T. Li, J. Liang, H. Yu and R. Zhou, "Dynamic Dictionary with Subconstant Wasted Bits per Key", Proceedings of the 2024 ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 171-207, 2024; arXiv:2310.20536.
