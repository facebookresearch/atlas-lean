# Basis matrix $P$ of $V$: identifiable on $\theta_0 + V$ iff $AP$ is

Let $A$ be a real $m \times n$ matrix, $P$ a real $n \times d$ matrix, $\theta_0 \in \mathbb{R}^n$
and $V$ a linear subspace of $\mathbb{R}^n$. Suppose that the columns of $P$ form a basis of $V$:
$P\xi \in V$ for every $\xi \in \mathbb{R}^d$, every $v \in V$ equals $P\xi$ for some
$\xi \in \mathbb{R}^d$, and $P\xi = 0$ implies $\xi = 0$. Then $A$ is
[identifiable on](identifiable-on-affine.md) the affine subspace
$\theta_0 + V = \{\theta : \theta - \theta_0 \in V\}$ if and only if the product $AP$ is
[identifiable](identifiable.md). So identifiability on an affine parameter space is
identifiability of an $m \times d$ matrix in basis coordinates. The proof combines the
[kernel criterion on $\theta_0 + V$](identifiable-on-affine-mk-iff-trivial-ke.md) with the
[kernel criterion for $AP$](identifiable-mul-basis-iff-trivial-ker.md).
