# Generalized Householder matrices

Let $v \in \mathbb{R}^n$ be a unit vector, let $\beta \in \mathbb{R}$ and let $H = I - \beta vv^{\mathsf T}$. Then $Hv = (1 - \beta) v$ and $H$ is the identity on the hyperplane $v^\perp$; $\det H = 1 - \beta$; for $n \ge 2$ the spectrum of $H$ is $\{1, 1 - \beta\}$; and $\|Hx\|_2^2 = \|x\|_2^2 - \beta(2 - \beta)(v^{\mathsf T} x)^2$ for every $x$, so the operator $2$-norm of $H$ is at most $1$ if and only if $\beta \in [0, 2]$.

## Idea

$H$ changes a vector only in the direction of $v$: it multiplies the component along $v$ by $1 - \beta$ and leaves the orthogonal complement fixed. Everything else follows. For $\beta = 1$ it is the orthogonal projection onto the hyperplane $v^\perp$, for $\beta = 2$ the Householder reflection across it, which numerical linear algebra uses to compute QR factorizations, and for $\beta \in (1, 2]$ it has a negative eigenvalue. The norm condition says when such a matrix is a contraction. Products of these matrices are the state transitions of delta-rule linear attention in sequence models.

## Statements

- [Spectrum, determinant and norm of a generalized Householder matrix](spectrum-one-sub-smul-vec-mul-vec.md)

## Related topics

- [Delta-rule linear attention](../../../ComputerScience/machine-learning/attention-and-low-rank-adaptation/delta-rule-linear-attention.md): products of such matrices are its state transitions.
