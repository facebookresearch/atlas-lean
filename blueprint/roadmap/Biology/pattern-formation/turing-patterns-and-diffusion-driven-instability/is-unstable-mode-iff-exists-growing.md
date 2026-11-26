# A Fourier mode grows iff $J - k^2 D$ has an eigenvalue with positive real part

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the Jacobian of the kinetics at a steady state) and let $d_u, d_v$ be real diffusion coefficients, and let $k \in \mathbb{R}$. The mode $k$ is [unstable](is-unstable-mode.md) if and only if there are
$\mu \in \mathbb{C}$ and a nonzero $v \in \mathbb{C}^2$ such that the [Fourier mode](fourier-mode.md)
$w(t, x) = e^{\mu t} \cos(kx)\, v$ is a [classical solution](is-linearized-solution.md) of
$w_t = D w_{xx} + J w$ and $\|w(t, 0)\| \to \infty$ as $t \to \infty$.
