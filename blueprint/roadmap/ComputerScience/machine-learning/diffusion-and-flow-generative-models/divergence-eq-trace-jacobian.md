# Divergence is the trace of the Jacobian

Let $n \ge 1$, let $F : \mathbb{R}^n \to \mathbb{R}^n$ have components $F_1, \dots, F_n$, and let
$x \in \mathbb{R}^n$. If $F$ is differentiable at $x$, then

$$\sum_{i=1}^{n} \partial_i F_i(x) = \operatorname{tr} DF(x),$$

where $\partial_i F_i(x) = DF_i(x) e_i$ is the partial derivative along the $i$-th standard basis
vector $e_i$ and $DF(x)$ is the derivative of $F$ at $x$, a linear map from $\mathbb{R}^n$ to
itself. In the computation of log-densities along a flow, the divergence of the velocity field is
written as this trace.

Proof: since $F$ is differentiable at $x$, so is each component $F_i$, the composite of $F$ with
the $i$-th coordinate projection, and $DF_i(x)$ is that projection composed with $DF(x)$. Hence
$\partial_i F_i(x)$ is the $i$-th coordinate of $DF(x) e_i$, the $(i, i)$ entry of the matrix of
$DF(x)$ in the standard basis, and the trace of a linear map is the sum of the diagonal entries of
its matrix.

The hypothesis cannot be dropped when, as in the conventions of both pages linked below, a
derivative that does not exist is taken to be $0$ (derived). For $F(x_1, x_2) = (x_1, |x_2|)$ at $x = 0$, the sum of
partial derivatives is $1 + 0 = 1$, since $|x_2|$ is not differentiable at $0$; but $F$ is not
differentiable at $0$, so its derivative is taken to be $0$, whose trace is $0$.

Two definitions of the divergence appear elsewhere: the divergence in the Fokker–Planck equation topic is the sum of
partial derivatives on $\mathbb{R}^n$, and the statement above equates it with the trace of the derivative
wherever $F$ is differentiable. The divergence in the Euler-equations singularity topic is defined directly
as the trace of the derivative of a field on three-dimensional Euclidean space. Identifying that
space with $\mathbb{R}^3$, a linear isomorphism that changes neither derivatives nor traces, the
statement with $n = 3$ shows that the two definitions agree at every point where the field is
differentiable. This is a reconciliation of two definitions, not one definition being an instance
of the other; where the field is not differentiable they can differ.

## Background

- [Divergence of a vector field](../../../Probability/stochastic-calculus/fokker-planck-equation/divergence.md):
  mathematical prerequisite, the sum-of-partial-derivatives definition that the statement equates
  with the trace of the derivative.
- [Divergence](../../../Analysis/partial-differential-equations/singularity-formation-for-the-euler-equations/div.md):
  background, the trace definition on three-dimensional Euclidean space, which agrees with the sum
  of partial derivatives for $n = 3$ at points of differentiability, after identifying that space
  with $\mathbb{R}^3$.

## Sources

- Y. Lipman, M. Havasi, P. Holderrieth, N. Shaul, M. Le, B. Karrer, R. T. Q. Chen, D. Lopez-Paz, H. Ben-Hamu and I. Gat, "Flow Matching Guide and Code", arXiv:2412.06264 (version 1), Section 3.6, equation (3.32), first equality (the divergence of the velocity field written as the trace of its Jacobian).
- AI-authored exposition.
