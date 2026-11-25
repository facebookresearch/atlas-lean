# Normal equations for the 3D-Var analysis

Let $n, m \in \mathbb{N}$, $B \in \mathbb{R}^{n \times n}$ and $R \in \mathbb{R}^{m \times m}$ positive definite, $H \in \mathbb{R}^{m \times n}$, $x_b \in \mathbb{R}^n$ and $y \in \mathbb{R}^m$. Let $J(x) = \tfrac12 (x - x_b)^{\top} B^{-1} (x - x_b) + \tfrac12 (H x - y)^{\top} R^{-1} (H x - y)$ and $x_a = x_b + B H^{\top} (H B H^{\top} + R)^{-1} (y - H x_b)$. Then $x_a$ satisfies the normal equations

$$(B^{-1} + H^{\top} R^{-1} H)(x_a - x_b) = H^{\top} R^{-1} (y - H x_b).$$
