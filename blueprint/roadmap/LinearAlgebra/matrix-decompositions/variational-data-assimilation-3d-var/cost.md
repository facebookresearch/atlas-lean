# 3D-Var cost function

For $n, m \in \mathbb{N}$, real matrices $B \in \mathbb{R}^{n \times n}$, $R \in \mathbb{R}^{m \times m}$, $H \in \mathbb{R}^{m \times n}$ and vectors $x_b \in \mathbb{R}^n$ (background), $y \in \mathbb{R}^m$ (observation), the 3D-Var cost of $x \in \mathbb{R}^n$ is

$$J(x) = \tfrac12 (x - x_b)^{\top} B^{-1} (x - x_b) + \tfrac12 (H x - y)^{\top} R^{-1} (H x - y),$$

with $B^{-1}$, $R^{-1}$ the inverses when invertible and the zero matrix by convention otherwise.
