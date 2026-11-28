# Kalman-form 3D-Var analysis

For $n, m \in \mathbb{N}$, real matrices $B \in \mathbb{R}^{n \times n}$, $R \in \mathbb{R}^{m \times m}$, $H \in \mathbb{R}^{m \times n}$ and vectors $x_b \in \mathbb{R}^n$, $y \in \mathbb{R}^m$, the Kalman-form analysis is

$$x_a = x_b + B H^{\top} (H B H^{\top} + R)^{-1} (y - H x_b),$$

with the inverse taken as the zero matrix by convention if $H B H^{\top} + R$ is singular.
