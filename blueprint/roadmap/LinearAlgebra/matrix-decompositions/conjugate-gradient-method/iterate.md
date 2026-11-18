# Conjugate gradient state after $k$ steps

For a real $n \times n$ matrix $A$, vectors $b, x_0 \in \mathbb{R}^n$ and $k \in \mathbb{N}$, the
$k$-th conjugate gradient state for the system $Ax = b$ from $x_0$ is obtained by applying the
[conjugate gradient step](step.md) $k$ times to the [initial state](init.md). Its first component
is the $k$-th iterate $x_k$.
