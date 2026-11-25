# A state-space layer with fixed parameters is a semiseparable matrix

Fix a parameter sequence $\theta = (A_t, B_t, C_t)_{0 \le t < T}$ with
$A_t \in \mathbb{R}^{N \times N}$ and $B_t, C_t \in \mathbb{R}^N$. The state-space recurrence
$h_t = A_t h_{t-1} + B_t x_t$, $y_t = C_t^{\mathsf{T}} h_t$, started from $h_0 = B_0 x_0$ and
acting on one scalar channel $x = (x_0, \dots, x_{T-1})$, satisfies $y = M_{\theta} x$, where
$M_{\theta}$ is the lower-triangular $T \times T$ matrix with entries
$(M_{\theta})_{ji} = C_j^{\mathsf{T}} A_j \cdots A_{i+1} B_i$ for $j \ge i$ (the identity for the
empty product when $j = i$). By the sequentially semiseparable representation, $M_{\theta}$ is
$N$-semiseparable. A layer with several channels or heads applies such a matrix to each channel.
This uses the convention of Dao and Gu, with no feed-through term.

Linear only for fixed parameters: in a selective state-space model such as Mamba or Mamba-2, the
step sizes and the vectors $B_t$ and $C_t$, hence also the discretized transitions $A_t$, are
computed from the input. The layer is then $x \mapsto M_{\theta(x)} x$, which in general is neither
linear nor time-invariant in $x$; the semiseparable structure is a property of $M_{\theta(x)}$ for each
fixed input.

Linear-time evaluation (derived): the steps compose as affine maps,
$(A', b') \circ (A, b) = (A' A, A' b + b')$, and this composition is associative, which is what
parallel prefix scans use. In floating point it is associative only up to rounding.

## Informally uses

- [Sequentially semiseparable matrices are semiseparable](../../../LinearAlgebra/special-matrices/semiseparable-matrices/is-semiseparable-of-sss.md):
  mathematical prerequisite, the "semiseparable" clause of the statement.

## Sources

- T. Dao and A. Gu, "Transformers are SSMs: Generalized Models and Efficient Algorithms Through Structured State Space Duality", arXiv:2405.21060 (version 1), Section 3.1, equation (3), and Section 3.3, Theorem 3.5.
- A. Gu and T. Dao, "Mamba: Linear-Time Sequence Modeling with Selective State Spaces", arXiv:2312.00752 (version 2), Section 3.2, Algorithm 2 (input-dependent parameters).
