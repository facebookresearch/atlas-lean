# Ply decomposition of the laminate energy

Let a laminate have interface heights $z_0, \dots, z_n \in \mathbb{R}$ and real $3 \times 3$ ply stiffness matrices $\bar Q_0, \dots, \bar Q_{n-1}$, and set

$$A = \sum_{i} (z_{i+1} - z_i)\,\bar Q_i, \qquad B = \sum_{i} \tfrac{1}{2}(z_{i+1}^2 - z_i^2)\,\bar Q_i, \qquad D = \sum_{i} \tfrac{1}{3}(z_{i+1}^3 - z_i^3)\,\bar Q_i.$$

Let $h_i = z_{i+1} - z_i$ and $\bar z_i = (z_i + z_{i+1})/2$. If every $\bar Q_i$ is symmetric, then for all $\varepsilon^0, \kappa \in \mathbb{R}^3$

$$\begin{pmatrix} \varepsilon^0 \\ \kappa \end{pmatrix}^{\!\top} \begin{pmatrix} A & B \\ B & D \end{pmatrix} \begin{pmatrix} \varepsilon^0 \\ \kappa \end{pmatrix} = \sum_{i=0}^{n-1} \Big( h_i\,(\varepsilon^0 + \bar z_i \kappa)^\top \bar Q_i\,(\varepsilon^0 + \bar z_i \kappa) + \frac{h_i^3}{12}\,\kappa^\top \bar Q_i\,\kappa \Big).$$
