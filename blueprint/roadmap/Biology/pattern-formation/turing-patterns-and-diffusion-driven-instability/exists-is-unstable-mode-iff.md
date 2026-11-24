# Turing's criterion

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the Jacobian of the kinetics at a steady state) and let $d_u, d_v$ be real diffusion coefficients, with $d_u > 0$ and $d_v > 0$, and suppose the steady state is stable without
diffusion: $\operatorname{tr} J < 0$ and $\det J > 0$. Then some Fourier mode $k \in \mathbb{R}$ is
[unstable](is-unstable-mode.md) if and only if $d_v f_u + d_u g_v > 2\sqrt{d_u d_v \det J}$.
