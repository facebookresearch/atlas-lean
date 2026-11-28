# Block-diagonal rotation matrices

For an integer $k \ge 1$, angles $\theta_1, \dots, \theta_k$ and $m \in \mathbb{R}$, let
$R_{\Theta}(m) \in \mathbb{R}^{2k \times 2k}$ be the block-diagonal matrix with the blocks
$R(m \theta_1), \dots, R(m \theta_k)$, where $R$ is the [planar rotation matrix](real-planar-rotation-matrices.md).
Then $R_{\Theta}(m)$ is orthogonal and $R_{\Theta}(m)^{\mathsf{T}} R_{\Theta}(n) = R_{\Theta}(n - m)$ for all
$m, n \in \mathbb{R}$.

Proof: block-diagonal matrices with blocks of the same sizes are multiplied and transposed block by block, so
$R_{\Theta}(m)^{\mathsf{T}} R_{\Theta}(n)$ is block-diagonal with the blocks
$R(m \theta_j)^{\mathsf{T}} R(n \theta_j) = R((n - m) \theta_j)$, by the
[identities of planar rotation matrices](rotation-matrix-identities.md); with $n = m$ this is the identity matrix.

## Depends on

- [Real planar rotation matrices](real-planar-rotation-matrices.md)

## Proof depends on

- [Identities of planar rotation matrices](rotation-matrix-identities.md)

## Sources

- J. Su, Y. Lu, S. Pan, A. Murtadha, B. Wen and Y. Liu, "RoFormer: Enhanced Transformer with Rotary Position Embedding", arXiv:2104.09864 (version 5), Section 3.2.2, equations (15)–(16) and the sentence after them: the block-diagonal rotary matrix $R^d_{\Theta, m}$, the identity $R^d_{\Theta, n - m} = (R^d_{\Theta, m})^{\mathsf{T}} R^d_{\Theta, n}$ and its orthogonality, with $\theta_i = 10000^{-2(i-1)/d}$ and integer positions.
