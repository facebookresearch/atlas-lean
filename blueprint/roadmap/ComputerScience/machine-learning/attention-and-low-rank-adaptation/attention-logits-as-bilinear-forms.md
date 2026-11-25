# Attention logits as bilinear forms

Let $d$, $d_h$ and $n_h$ be positive integers. In multi-head attention, a layer maps each hidden
state $h_t \in \mathbb{R}^d$ to a query $W^Q h_t$ and a key $W^K h_t$ with
$W^Q, W^K \in \mathbb{R}^{d_h n_h \times d}$, and head $i$ uses the $i$-th blocks of $d_h$
coordinates, $q_{t,i} = W^Q_i h_t$ and $k_{t,i} = W^K_i h_t$ with
$W^Q_i, W^K_i \in \mathbb{R}^{d_h \times d}$. Before causal masking and the softmax, the logit
of head $i$ between positions $t$ and $j$ is
$q_{t,i}^{\mathsf{T}} k_{j,i} / \sqrt{d_h} = h_t^{\mathsf{T}} M_i h_j / \sqrt{d_h}$ with
$M_i = (W^Q_i)^{\mathsf{T}} W^K_i \in \mathbb{R}^{d \times d}$.

So, up to the factor $1/\sqrt{d_h}$, the logit is the bilinear form
$(x, y) \mapsto x^{\mathsf{T}} M_i y$ on $\mathbb{R}^d$, and $M_i$ is the matrix representing it
in the standard basis. Since $M_i$ is a product of matrices through $\mathbb{R}^{d_h}$, its rank,
and so the rank of the form, is at most $d_h$ (derived). For $L \ge 1$ hidden states stacked as
the rows of $H \in \mathbb{R}^{L \times d}$, the $L \times L$ logit matrix
$H M_i H^{\mathsf{T}} / \sqrt{d_h}$ has rank at most $\min(d_h, L)$.

Caveats (derived; the paper states the attention equations, not these bounds):

- $M_i$ need not be symmetric, so a logit matrix is in general not a Gram matrix and need not be
  positive semidefinite; it is one in special cases, for example when $W^Q_i = W^K_i$.
- The rank bounds concern the real logit matrix before masking and softmax. A causal mask
  excludes entries, or sets them to $-\infty$, and the bounds say nothing about the masked array.
  After the row-wise softmax, every row with at least one allowed finite logit is a probability
  vector, so the attention matrix is row-stochastic on those rows; since softmax is not linear,
  it need not have rank at most $d_h$.
-  With rotary position embedding there is in general no single position-independent matrix $M_i$,
  but when the rotation acts within each head's $d_h$ coordinates ($d_h$ even), the logit matrix is
  still the product of the rotated queries and keys, of width $d_h$, so its rank is still at most
  $\min(d_h, L)$.
- Illustration: with DeepSeek-V2's dimensions $d = 5120$ and $d_h = 128$, a standard multi-head
  layer of that shape has $5120 \times 5120$ matrices $M_i$ of rank at most $128$; DeepSeek-V2
  itself uses multi-head latent attention, whose content logits satisfy the same bound.

## Informally uses

- [Rank of a product of matrices](../../../LinearAlgebra/linear-maps-and-duality/rank-of-a-matrix-product/rank-of-a-product.md):
  mathematical prerequisite, the bound $\operatorname{rank} M_i \le d_h$.

## Background

- [Rank of a bilinear form](../../../LinearAlgebra/bilinear-and-quadratic-forms/rank-of-a-bilinear-form/bilin-form-rank.md):
  background, which defines the rank of a bilinear form as the rank of its matrix in a basis
  (that page's Gram matrix $(B(b_i, b_j))$); in the standard basis this matrix is $M_i$.

## Sources

- DeepSeek-AI, "DeepSeek-V2: A Strong, Economical, and Efficient Mixture-of-Experts Language Model", arXiv:2405.04434 (version 5), Section 2.1.1, equations (1)–(8) (multi-head attention), and Section 3.1.2 (model hyper-parameters).
