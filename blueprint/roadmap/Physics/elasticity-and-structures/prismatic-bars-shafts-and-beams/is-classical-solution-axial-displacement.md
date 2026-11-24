# The rescaled uniform-load bar displacement is a classical solution

Let $EA > 0$ and let $L$ and $q$ be any real numbers. The rescaled
[axial displacement](axial-displacement.md)

$$v(\xi) = \frac{q\, (L\xi)\, (L - L\xi)}{2\, EA} = \frac{q\, L^2\, \xi\, (1 - \xi)}{2\, EA}$$

is a
[classical solution](../../../Analysis/numerical-analysis/finite-element-method-in-one-dimension/is-classical-solution.md)
of the Dirichlet problem $-v'' = L^2 q / EA$ on $(0, 1)$, $v(0) = v(1) = 0$: $v$ is twice
continuously differentiable on $\mathbb{R}$, the constant right side is continuous,
$v(0) = v(1) = 0$, and $-v''(\xi) = L^2 q/EA$ for every $\xi \in (0, 1)$. No condition on $L$ is
needed.
