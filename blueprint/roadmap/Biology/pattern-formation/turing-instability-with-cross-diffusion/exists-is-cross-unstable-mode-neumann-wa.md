# Under the cross-diffusion criterion, long intervals have unstable k_n

Let $J$ and $D$ be real $2 \times 2$ matrices (the Jacobian of the kinetics at a homogeneous steady
state and a diffusion matrix, possibly non-diagonal). Assume $\operatorname{tr} J < 0$ and
$\det J > 0$, $\operatorname{tr} D \ge 0$ and $\det D > 0$, and $2 \sqrt{\det D \det J} < b$ with
$b = J_{00} D_{11} + J_{11} D_{00} - J_{01} D_{10} - J_{10} D_{01}$. Then there is $L_0 > 0$ such
that for every $L \ge L_0$ some $n \ge 1$ has a [linearly unstable](is-cross-unstable-mode.md)
Fourier mode at the
[Neumann wavenumber](../turing-patterns-and-diffusion-driven-instability/neumann-wavenumber.md)
$k_n = n\pi/L$: on every long enough interval $[0, L]$ some non-homogeneous Neumann mode is
unstable, while the homogeneous mode is [stable](not-is-cross-unstable-mode-zero.md).
