# Minimal Keller–Segel: k ≠ 0 is unstable iff d_u d_v k² < αχu₀ − βd_u

Let $\beta > 0$, $d_u, d_v \ge 0$, let $\alpha$, $\chi$ and $u_0$ be real, and let $k \neq 0$. For
the minimal Keller–Segel Jacobian $\begin{pmatrix} 0 & 0 \\ \alpha & -\beta \end{pmatrix}$ ($r = 0$,
the Jacobian at every steady state $(u_0, \alpha u_0/\beta)$) and the
[diffusion matrix](keller-segel-diffusion.md)
$D = \begin{pmatrix} d_u & -\chi u_0 \\ 0 & d_v \end{pmatrix}$ at cell density $u_0$, the Fourier
mode of wavenumber $k$ is [linearly unstable](is-cross-unstable-mode.md) if and only if

$$d_u d_v k^2 < \alpha \chi u_0 - \beta d_u.$$

Its long-wave limit is the classical chemotactic instability condition
$\alpha \chi u_0 > \beta d_u$. In the model $\alpha > 0$, $\chi \ge 0$ and $u_0 \ge 0$; the
equivalence holds for all real values.
