# For stable kinetics, d_u, d_v > 0: no unstable mode on short intervals

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the
Jacobian of the kinetics at a homogeneous steady state) with $\operatorname{tr} J < 0$ and
$\det J > 0$ (kinetics stable without diffusion), and let $d_u, d_v > 0$. Then there is $L_1 > 0$
such that for every $L$ with $0 < L \le L_1$ the homogeneous steady state is not [linearly unstable
on $[0, L]$](is-neumann-unstable.md): no Neumann mode $\cos(n\pi x/L)$ is unstable.
