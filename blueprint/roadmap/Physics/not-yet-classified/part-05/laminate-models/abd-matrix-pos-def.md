# Laminate stiffness matrix is positive definite

Let a laminate have interface heights $z_0, \dots, z_n \in \mathbb{R}$ and real $3 \times 3$ ply stiffness matrices $\bar Q_0, \dots, \bar Q_{n-1}$, and set

$$A = \sum_{i} (z_{i+1} - z_i)\,\bar Q_i, \qquad B = \sum_{i} \tfrac{1}{2}(z_{i+1}^2 - z_i^2)\,\bar Q_i, \qquad D = \sum_{i} \tfrac{1}{3}(z_{i+1}^3 - z_i^3)\,\bar Q_i.$$

If $n \ge 1$, $z_0 < z_1 < \dots < z_n$ and every $\bar Q_i$ is symmetric positive definite, then the $6 \times 6$ matrix $\begin{pmatrix} A & B \\ B & D \end{pmatrix}$ is positive definite.
