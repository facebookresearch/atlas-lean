# Time-invariant state-space layers are lower-triangular Toeplitz matrices

If the parameters of a state-space layer are constant, $A_t = A$, $B_t = B$ and $C_t = C$, then the
matrix of the layer has entries $M_{ji} = C^{\mathsf{T}} A^{j-i} B$ for $j \ge i$ and $0$ for
$j < i$. They depend only on $j - i$, so $M$ is the leading $T \times T$ block of the
lower-triangular Toeplitz matrix of the kernel $K_k = C^{\mathsf{T}} A^k B$, $k = 0, 1, 2, \dots$,
and the layer is the causal convolution $y_j = \sum_{i \le j} K_{j-i} x_i$.

Conventions: this uses the recurrence $h_t = A h_{t-1} + B x_t$, $y_t = C^{\mathsf{T}} h_t$ of the
general page, with no feed-through term. With a feed-through term $D x_t$ the first kernel entry
becomes $C^{\mathsf{T}} B + D$; under the classical convention $h_{t+1} = A h_t + B x_t$,
$y_t = C h_t + D x_t$ the kernel is $(D, CB, CAB, \dots)$. The Toeplitz matrix page indexes rows
and columns by $\mathbb{N}$, so the layer's matrix is its restriction to the first $T$ indices.
Selective models, whose parameters depend on the input, need not be time-invariant, and their
matrices need not be Toeplitz.

## Informally uses

- [A state-space layer with fixed parameters is a semiseparable matrix](ssm-matrix-form.md):
  special case of, with constant parameters.

## Background

- [Lower-triangular Toeplitz matrix](../../../LinearAlgebra/special-matrices/toeplitz-matrices/lower-toeplitz.md):
  mathematical prerequisite, the definition used in the statement.

## Sources

- A. Gu and T. Dao, "Mamba: Linear-Time Sequence Modeling with Selective State Spaces", arXiv:2312.00752 (version 2), Section 2, equations (2a)–(3b) and the paragraph on linear time invariance.
