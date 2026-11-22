# The conjugate gradient error bound in terms of the condition number

Let $n \ge 1$, let $A$ be a real symmetric positive definite $n \times n$ matrix with
[spectral condition number](cond-num.md) $\kappa = \lambda_{\max} / \lambda_{\min}$, let
$b, x^\star \in \mathbb{R}^n$ with $A x^\star = b$, and let $x_0 \in \mathbb{R}^n$. Then for every
$k \in \mathbb{N}$, the $k$-th [conjugate gradient iterate](iterate.md) $x_k$ for $Ax = b$ from
$x_0$ satisfies

$$\|x_k - x^\star\|_A \le 2 \left(\frac{\sqrt{\kappa} - 1}{\sqrt{\kappa} + 1}\right)^k
\|x_0 - x^\star\|_A,$$

where $\|\cdot\|_A$ is the [energy norm](energy-norm.md).
