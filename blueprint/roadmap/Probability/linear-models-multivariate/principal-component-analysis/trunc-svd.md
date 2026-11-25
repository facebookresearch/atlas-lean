# Truncated singular value decomposition

Let $A$ be a real $m \times n$ matrix with [right singular vectors](right-singular-basis.md) $v_0, \dots, v_{n-1}$ and $k \in \mathbb{N}$. The rank-$k$ truncated singular value decomposition is

$$A_k = A \sum_{i < \min(k, n)} v_i v_i^\top = \sum_{i < \min(k,n)} \sigma_i u_i v_i^\top,$$

where $u_i = A v_i / \sigma_i$ for $\sigma_i > 0$ (terms with $\sigma_i = 0$ vanish).
