# Dispersion relation

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the Jacobian of the kinetics at a steady state) and let $d_u, d_v$ be real diffusion coefficients. For real $k$, $\mu \in \mathbb{C}$ and $v \in \mathbb{C}^2$, the
[Fourier mode](fourier-mode.md) $w(t, x) = e^{\mu t} \cos(kx)\, v$ is a
[classical solution](is-linearized-solution.md) of the linearized system $w_t = D w_{xx} + J w$,
$D = \operatorname{diag}(d_u, d_v)$, if and only if $(J - k^2 D) v = \mu v$.
