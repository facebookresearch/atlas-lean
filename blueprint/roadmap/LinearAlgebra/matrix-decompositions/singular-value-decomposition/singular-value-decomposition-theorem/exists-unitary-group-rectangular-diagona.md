# Complex SVD with nonincreasing singular values

Let $m, n \in \mathbb{N}$. Every complex $m \times n$ matrix $A$ factors as $A = U \Sigma V^*$, where
$U$ and $V$ are unitary matrices of sizes $m$ and $n$, and $\Sigma$ is the $m \times n$ matrix with
$\Sigma_{jj} = \sigma_j$ and all other entries $0$, for real numbers
$\sigma_1 \ge \sigma_2 \ge \dots \ge \sigma_n \ge 0$ with $\sigma_j = 0$ whenever $j > m$. This is the
rectangular complex singular value decomposition with the singular values in nonincreasing order.

Proof: multiply the factorization $AV = U\Sigma$, with the same $U$, $V$ and $\Sigma$, on the right by $V^*$, using $V V^* = I$.
