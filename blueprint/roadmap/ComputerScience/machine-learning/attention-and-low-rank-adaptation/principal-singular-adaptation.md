# Principal singular values and vectors adaptation (PiSSA)

PiSSA keeps the adapter architecture of low-rank adaptation and changes its initialisation. Let
$W \in \mathbb{R}^{m \times n}$ be a pretrained weight matrix with an economy singular value
decomposition $W = U S V^{\mathsf{T}}$ whose singular values $s_1 \ge s_2 \ge \dots \ge 0$ are in
nonincreasing order, and let $1 \le r \le \min(m, n)$. PiSSA sets
$A = U_{[:, :r]} S_{[:r, :r]}^{1/2} \in \mathbb{R}^{m \times r}$ and
$B = S_{[:r, :r]}^{1/2} V_{[:, :r]}^{\mathsf{T}} \in \mathbb{R}^{r \times n}$, freezes the
residual $W^{res} = U_{[:, r:]} S_{[r:, r:]} V_{[:, r:]}^{\mathsf{T}}$, and trains $A$ and $B$.
In exact arithmetic $W = W^{res} + AB$, so training starts from the pretrained weight, and
$AB = U_{[:, :r]} S_{[:r, :r]} V_{[:, :r]}^{\mathsf{T}}$ is a rank-$r$ truncated singular value
decomposition of $W$.

Uniqueness (derived): a strict gap $s_r > s_{r+1}$ is sufficient for the truncation $AB$, and
with it $W^{res}$, to be unique. If $\operatorname{rank} W \le r$, the truncation is $AB = W$,
again unique. For $r < \operatorname{rank} W$, the truncation is unique if and only if
$s_r > s_{r+1}$. The factors themselves are never unique when $W \ne 0$: changing the signs of a
singular pair $(u_i, v_i)$ with $s_i > 0$ changes $A$ and $B$ but not $AB$, and repeated singular
values add orthogonal freedom.

In practice the paper computes the decomposition with a randomised fast SVD algorithm, which only
approximates it: its appendix reports a nonzero initialisation error that decreases with the
number of subspace iterations. The exact identity $W = W^{res} + AB$ above is the
exact-arithmetic definition, not a property of that approximate computation.

The letters are swapped relative to low-rank adaptation: PiSSA's $A$ has $r$ columns and its $B$
has $r$ rows.

## Informally uses

- [Real singular value decomposition with nonincreasing singular values](../../../LinearAlgebra/matrix-decompositions/singular-value-decomposition/exists-orthogonal-group-rectangular-diag.md):
  mathematical prerequisite, the existence of the ordered decomposition from which the
  initialisation is defined (its first $\min(m, n)$ columns give the economy form).
- [Truncated singular value decomposition](../../../Probability/linear-models-multivariate/principal-component-analysis/trunc-svd.md):
  mathematical prerequisite, since $AB$ is the rank-$r$ truncated decomposition, which equals
  $W V_{[:, :r]} V_{[:, :r]}^{\mathsf{T}}$ for the same decomposition; that page sits in the
  principal component analysis chapter.
- [Low-rank adaptation (LoRA)](low-rank-adaptation.md): builds on, the same adapter architecture,
  with a different initialisation and a frozen residual in place of the frozen pretrained weight.

## Sources

- F. Meng, Z. Wang and M. Zhang, "PiSSA: Principal Singular Values and Singular Vectors Adaptation of Large Language Models", arXiv:2404.02948 (version 4), Section 3, equations (2)–(5), Appendix B (fast SVD and its initialisation error) and Appendix C.
