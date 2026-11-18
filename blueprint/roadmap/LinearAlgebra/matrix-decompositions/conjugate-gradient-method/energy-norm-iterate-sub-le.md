# The conjugate gradient error bound

Let $A$ be a real symmetric positive definite $n \times n$ matrix whose eigenvalues all lie in
$[a, c]$ with $a > 0$, let $b, x^\star \in \mathbb{R}^n$ with $A x^\star = b$, and let
$x_0 \in \mathbb{R}^n$. Then for every $k \in \mathbb{N}$, the $k$-th
[conjugate gradient iterate](iterate.md) $x_k$ for $Ax = b$ from $x_0$ satisfies

$$\|x_k - x^\star\|_A \le 2 \left(\frac{\sqrt{\kappa} - 1}{\sqrt{\kappa} + 1}\right)^k
\|x_0 - x^\star\|_A, \qquad \kappa = c/a,$$

where $\|\cdot\|_A$ is the [energy norm](energy-norm.md).
