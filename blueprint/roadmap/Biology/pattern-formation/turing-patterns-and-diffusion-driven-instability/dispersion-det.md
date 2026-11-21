# Dispersion polynomial

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the Jacobian of the kinetics at a steady state) and let $d_u, d_v$ be real diffusion coefficients. The dispersion polynomial is

$$h(q) = d_u d_v q^2 - (d_v f_u + d_u g_v)\, q + \det J \qquad (q \in \mathbb{R}),$$

so that the [mode matrix](mode-matrix.md) satisfies $\det(J - k^2 D) = h(k^2)$
([determinant of the mode matrix](det-mode-matrix.md)).
