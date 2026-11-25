# Turing's criterion with cross-diffusion: 2√(det D det J) < b

Let $J$ and $D$ be real $2 \times 2$ matrices (the Jacobian of the kinetics at a homogeneous steady
state and a diffusion matrix, possibly non-diagonal). Assume $\operatorname{tr} J < 0$ and
$\det J > 0$ (kinetics stable without diffusion), and $\operatorname{tr} D \ge 0$ and $\det D > 0$.
Then some real wavenumber $k$ gives a [linearly unstable](is-cross-unstable-mode.md) Fourier mode if
and only if

$$2 \sqrt{\det D \det J} < b,$$

where $b = J_{00} D_{11} + J_{11} D_{00} - J_{01} D_{10} - J_{10} D_{01}$ is the
[mixed coefficient](cross-coeff.md).

The hypotheses on $D$ do not make the diffusion parabolic:
$D = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}$ satisfies them. A normally parabolic $D$
($\operatorname{tr} D > 0$, $\det D > 0$) is a special case.
