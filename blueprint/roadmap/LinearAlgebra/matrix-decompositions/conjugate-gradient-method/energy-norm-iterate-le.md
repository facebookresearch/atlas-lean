# CG minimizes the energy norm of the error over the Krylov space

Let $A$ be a real symmetric positive definite $n \times n$ matrix, let $b, x^\star \in \mathbb{R}^n$
with $A x^\star = b$, let $x_0 \in \mathbb{R}^n$ and $k \in \mathbb{N}$, and let $x_k$ be the $k$-th
[conjugate gradient iterate](iterate.md) for $Ax = b$ from $x_0$. Then

$$\|x_k - x^\star\|_A \le \|x_0 + z - x^\star\|_A$$

for every $z$ in the [Krylov space](krylov.md) $\mathcal{K}_k(A, r_0)$, $r_0 = b - A x_0$: the
iterate minimizes the [energy norm](energy-norm.md) of the error over $x_0 + \mathcal{K}_k(A, r_0)$.
