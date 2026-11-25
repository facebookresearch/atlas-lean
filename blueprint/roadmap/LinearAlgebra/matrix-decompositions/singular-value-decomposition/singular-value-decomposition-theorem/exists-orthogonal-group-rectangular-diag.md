# Real singular value decomposition with nonincreasing singular values

Let $A$ be a real
$m \times n$ matrix. Then there are orthogonal matrices $U$ of size $m \times m$ and $V$ of size
$n \times n$ and real numbers $\sigma_1 \ge \sigma_2 \ge \dots \ge \sigma_n \ge 0$ with
$\sigma_j = 0$ for every $j > m$, such that $A = U \Sigma V^{\mathsf{T}}$, where $\Sigma$ is the
$m \times n$ matrix with $\Sigma_{jj} = \sigma_j$ for $j \le \min(m, n)$ and all other entries
zero.

Proof: multiply the factorization $AV = U\Sigma$ on the right by $V^{\mathsf{T}}$.
