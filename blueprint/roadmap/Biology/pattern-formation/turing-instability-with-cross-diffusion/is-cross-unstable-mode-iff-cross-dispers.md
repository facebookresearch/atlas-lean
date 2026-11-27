# For tr J < 0 and tr D ≥ 0, a mode is unstable iff h(k²) < 0

Let $J$ and $D$ be real $2 \times 2$ matrices (the Jacobian of the kinetics at a homogeneous steady
state and a diffusion matrix, possibly non-diagonal), with $\operatorname{tr} J < 0$ and
$\operatorname{tr} D \ge 0$, and let $k$ be real. Then the Fourier mode of wavenumber $k$ is
[linearly unstable](is-cross-unstable-mode.md) if and only if $h(k^2) < 0$, where the
[dispersion polynomial](cross-dispersion-det.md) is $h(q) = \det D\, q^2 - b\, q + \det J$ and
$b = J_{00} D_{11} + J_{11} D_{00} - J_{01} D_{10} - J_{10} D_{01}$.
