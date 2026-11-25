# Rotary position embedding (RoPE)

Let $d$ be a positive even integer and $\theta_1, \dots, \theta_{d/2}$ real angles; RoFormer uses
$\theta_i = 10000^{-2(i-1)/d}$. For a position $m \in \mathbb{Z}$, let
$R_m \in \mathbb{R}^{d \times d}$ be the block-diagonal matrix with the $2 \times 2$ rotation blocks
$R(m\theta_1), \dots, R(m\theta_{d/2})$. For a positive integer $p$, token representations
$x_m, x_n \in \mathbb{R}^p$ and projections $W_q, W_k \in \mathbb{R}^{d \times p}$, rotary position
embedding multiplies the projected query of the token at position $m$ and the projected key of the
token at position $n$ by these matrices: $q_m = R_m W_q x_m$ and $k_n = R_n W_k x_n$. Values are not
rotated. In multi-head attention, $d$ is the width of one head and each head's query and key are
rotated separately with these angles.

Relative positions (derived here from the definitions): each block satisfies
$R(a)^{\mathsf{T}} R(b) = R(b - a)$, so $R_m^{\mathsf{T}} R_n = R_{n-m}$ and
$q_m^{\mathsf{T}} k_n = x_m^{\mathsf{T}} W_q^{\mathsf{T}} R_{n-m} W_k x_n$. For fixed $x_m$ and
$x_n$, the logit therefore depends on the two positions only through the offset $n - m$. For
$d = 2$, identifying $\mathbb{R}^2$ with $\mathbb{C}$, where $\langle z, w \rangle =
\operatorname{Re}(z \bar{w})$, and with $\theta = \theta_1$, this is
$\operatorname{Re}\big[(W_q x_m) \overline{(W_k x_n)} e^{i(m - n)\theta}\big]$, the complex form
in which RoFormer introduces the method.

The rotations are orthogonal, so they preserve the norms of queries and keys. The logit is the
bilinear form in $(x_m, x_n)$ with matrix $W_q^{\mathsf{T}} R_{n-m} W_k$, which depends on the
offset: for generic weights and angles it changes with $n - m$, so there is in general no single
position-independent matrix, although special cases exist (for example zero weights, or angles for
which the rotations at the offsets considered are the identity). The logit matrix is still the
product of the rotated queries and keys, of width $d$, so for $L \ge 1$ positions its rank is at
most $\min(d, L)$.

$R_m v$ can be computed without forming the $d \times d$ matrix $R_m$: it is the sum of the
elementwise product of $v$ with
$(\cos m\theta_1, \cos m\theta_1, \dots, \cos m\theta_{d/2}, \cos m\theta_{d/2})$ and the
elementwise product of $(-v_2, v_1, \dots, -v_d, v_{d-1})$ with the corresponding vector of sines.
The paper's long-term-decay argument is analysis and is not covered here.

## Informally uses

- [Identities of planar rotation matrices](../../../LinearAlgebra/special-matrices/rotation-matrices/rotation-matrix-identities.md):
  mathematical prerequisite, the composition law and the transpose of the rotation blocks.
- [Block-diagonal rotation matrices](../../../LinearAlgebra/special-matrices/rotation-matrices/block-diagonal-rotations.md):
  mathematical prerequisite, the relative-position identity of the block-diagonal rotations.
- [Attention logits as bilinear forms](attention-logits-as-bilinear-forms.md): builds on, since
  RoPE changes the query and key factors of the logit's bilinear form.

## Sources

- J. Su, Y. Lu, S. Pan, A. Murtadha, B. Wen and Y. Liu, "RoFormer: Enhanced Transformer with Rotary Position Embedding", arXiv:2104.09864 (version 5), Section 3.2.1, equations (12)–(13), Section 3.2.2, equations (14)–(16), and Section 3.4.2, equation (34).
