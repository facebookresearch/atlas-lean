# For tr J < 0, an admissible mode is unstable iff d_n(k²) < d

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the
Jacobian of the kinetics at a homogeneous steady state) with $\operatorname{tr} J < 0$, and let
$d_u \ge 0$, $d \ge 0$ and $D(d) = \operatorname{diag}(d_u, d)$. Let $k$ be an admissible
wavenumber: $f_u k^2 - d_u k^4 > 0$. Then the Fourier mode of wavenumber $k$ is
[linearly unstable](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/is-unstable-mode.md)
for the diffusion matrix $D(d)$ if and only if $d_n(k^2) < d$, where
$d_n(q) = (\det J - d_u g_v q)/(f_u q - d_u q^2)$ is the [neutral diffusion](neutral-diffusion.md).
