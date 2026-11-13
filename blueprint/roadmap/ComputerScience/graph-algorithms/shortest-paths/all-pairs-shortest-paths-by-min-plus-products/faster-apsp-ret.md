# FASTER-APSP returns a power of the input matrix

Let $\alpha$ be a semiring, let $W$ be
an $n \times n$ matrix over $\alpha$, and let $k = \lceil \log_2 (n - 1) \rceil$ be the least
natural number with $n - 1 \le 2^k$ (so $k = 0$ when $n \le 2$). The matrix returned by
FASTER-APSP on $W$ is the matrix power $W^{2^k}$, with products computed in $\alpha$.
