# For r, β, d_u, d_v > 0, chemotactic instability criterion at (1, α/β)

Let $r, \beta, d_u, d_v > 0$ and $\alpha, \chi$ be real. For the Keller–Segel
[Jacobian](keller-segel-jacobian.md) $J = \begin{pmatrix} -r & 0 \\ \alpha & -\beta \end{pmatrix}$
at $(1, \alpha/\beta)$ and the [diffusion matrix](keller-segel-diffusion.md)
$D = \begin{pmatrix} d_u & -\chi u_0 \\ 0 & d_v \end{pmatrix}$ at $u_0 = 1$, some real wavenumber
$k$ gives a [linearly unstable](is-cross-unstable-mode.md) Fourier mode if and only if

$$2 \sqrt{d_u d_v r \beta} < \alpha \chi - r d_v - \beta d_u.$$

The state is stable for the kinetics alone ($\operatorname{tr} J = -r - \beta < 0$,
$\det J = r\beta > 0$). In the model $\alpha > 0$ and $\chi \ge 0$; the equivalence holds for all
real $\alpha$ and $\chi$.
