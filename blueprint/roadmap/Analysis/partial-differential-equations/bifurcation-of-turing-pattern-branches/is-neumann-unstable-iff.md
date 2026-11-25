# Instability on an interval is instability of some Neumann mode

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the
Jacobian of the kinetics at a homogeneous steady state), let $d_u, d_v$ be real and
$D = \operatorname{diag}(d_u, d_v)$, and let $L$ be real. The homogeneous steady state is [linearly
unstable on $[0, L]$](is-neumann-unstable.md) if and only if, for some $n \in \mathbb{N}$, the
Fourier mode with the
[Neumann wavenumber](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/neumann-wavenumber.md)
$k_n = n\pi/L$ is
[linearly unstable](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/is-unstable-mode.md):
the mode matrix $J - k_n^2 D$ has a complex eigenvalue with positive real part.

In the model $d_u, d_v > 0$ and $L > 0$; the statement holds for all real values.
