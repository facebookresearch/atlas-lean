# Delta-rule linear attention

DeltaNet is a linear transformer whose matrix-valued state $S_t \in \mathbb{R}^{d \times d}$ is
updated by the delta rule
$S_t = S_{t-1} - \beta_t (S_{t-1} k_t - v_t) k_t^{\mathsf{T}}
= S_{t-1} (I - \beta_t k_t k_t^{\mathsf{T}}) + \beta_t v_t k_t^{\mathsf{T}}$, with keys and values
$k_t, v_t \in \mathbb{R}^d$, writing strength $\beta_t = \sigma(W_{\beta} x_t) \in (0, 1)$ and
output $o_t = S_t q_t$. Each step multiplies the state on the right by the identity-plus-rank-one
matrix $I - \beta_t k_t k_t^{\mathsf{T}}$, a generalized Householder matrix, and adds a rank-one
matrix. Keys are normalised to unit Euclidean norm,
$k_t = \mathrm{SiLU}(W_K x_t) / \|\mathrm{SiLU}(W_K x_t)\|_2$, which presupposes that
$\mathrm{SiLU}(W_K x_t) \ne 0$.

Spectrum of the transitions (derived): for a nonzero key $k$, $d \ge 2$ and real $\beta \ne 0$,
$I - \beta k k^{\mathsf{T}}$ is symmetric with the eigenvalue $1$ of multiplicity $d - 1$ on
$k^{\perp}$ and the simple eigenvalue $1 - \beta \|k\|_2^2$ on $k$. The paper prints the second
eigenvalue as $1 - \beta_t \|k_t\|_2$; the eigenvalue is $1 - \beta_t \|k_t\|_2^2$, which equals
$1 - \beta_t$ for its unit-norm keys.

With unit keys and $\beta_t \in (0, 1)$, every transition therefore has eigenvalues in $(0, 1]$ and,
being symmetric, spectral norm at most $1$ (exactly $1$ when $d \ge 2$). Since the spectral norm is
submultiplicative, every product of transitions has norm at most $1$, so for a fixed input
sequence (fixed keys and writing strengths) a perturbation of the state is never amplified as it
propagates; the per-step eigenvalue condition suffices here only because the transitions are
symmetric. The orthogonal projection onto $k_t^{\perp}$ would need $\beta_t = 1$, the boundary of
the sigmoid's range, which is approached but not attained; the Householder reflection would need
$\beta_t = 2$, outside DeltaNet's range, and is reached only by the extension of Grazzi et al. to
$\beta_t \in [0, 2]$.

## Informally uses

- [Spectrum of a generalized Householder matrix](../../../LinearAlgebra/special-matrices/generalized-householder-matrices/spectrum-one-sub-smul-vec-mul-vec.md):
  mathematical prerequisite, the spectrum of the transition $I - \beta_t k_t k_t^{\mathsf{T}}$.
- [When a generalized Householder matrix is a contraction](../../../LinearAlgebra/special-matrices/generalized-householder-matrices/l2-op-norm-one-sub-smul-vec-mul-vec-le-o.md):
  mathematical prerequisite, the norm of the transition $I - \beta_t k_t k_t^{\mathsf{T}}$.

## Sources

- S. Yang, B. Wang, Y. Zhang, Y. Shen and Y. Kim, "Parallelizing Linear Transformers with the Delta Rule over Sequence Length", arXiv:2406.06484 (version 6), Section 2.2 (the delta rule and $\beta_t \in (0, 1)$), Section 3.1 (the update written with the transition $I - \beta_t k_t k_t^{\mathsf{T}}$, in the induction step leading to equation (3)), and Section 3.3 (key normalisation and the eigenvalues).
- R. Grazzi, J. Siems, A. Zela, J. K. H. Franke, F. Hutter and M. Pontil, "Unlocking State-Tracking in Linear RNNs Through Negative Eigenvalues", ICLR 2025, arXiv:2411.12537 (version 5), Section 4.2, equation (2).
