# Lyapunov vector field of the limit covariance

For real $\beta$, $\gamma$, a point $p = (s, i)$ and a symmetric $2 \times 2$ matrix stored as a
triple $c = (c_1, c_2, c_3)$, standing for $\begin{pmatrix} c_1 & c_2 \\ c_2 & c_3 \end{pmatrix}$,
the Lyapunov field is

$$L_p(V) = DF(p)\, V + V\, DF(p)^{\mathsf T} + G(p),$$

stored as a triple in the same way, with the [Jacobian](jacobian.md) $DF(p)$ and the
[infinitesimal covariance](diffusion-matrix.md) $G(p)$. The columns of $DF(p)\, V$ are $DF(p)$
applied to the columns $(c_1, c_2)$ and $(c_2, c_3)$ of $V$; its
[coordinates](lyapunov-field-apply.md) are explicit.
