# CG stays in the Krylov space

Let $A$ be a real $n \times n$ matrix, let $b, x_0 \in \mathbb{R}^n$, and let $x_k$ be the $k$-th
[conjugate gradient iterate](iterate.md) for the system $Ax = b$ from $x_0$. Then for every
$k \in \mathbb{N}$, $x_k - x_0$ lies in the [Krylov space](krylov.md) $\mathcal{K}_k(A, r_0)$, where
$r_0 = b - A x_0$. No hypothesis on $A$ is needed.
