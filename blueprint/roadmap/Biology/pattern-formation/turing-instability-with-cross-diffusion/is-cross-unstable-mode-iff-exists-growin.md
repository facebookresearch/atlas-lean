# A mode is unstable iff it carries a growing Fourier-mode solution

Let $J$ and $D$ be real $2 \times 2$ matrices (the Jacobian of the kinetics at a homogeneous steady
state and a diffusion matrix, possibly non-diagonal), and let $k$ be real. The Fourier mode of
wavenumber $k$ is [linearly unstable](is-cross-unstable-mode.md) if and only if there are
$\mu \in \mathbb{C}$ and a nonzero $v \in \mathbb{C}^2$ such that
$w(t, x) = e^{\mu t} \cos(k x)\, v$ is a [classical solution](is-cross-linearized-solution.md) of
$w_t = D w_{xx} + J w$ and $\lVert w(t, 0) \rVert \to \infty$ as $t \to \infty$.
