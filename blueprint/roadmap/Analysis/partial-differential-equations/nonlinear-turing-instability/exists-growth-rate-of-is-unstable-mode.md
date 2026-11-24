# For tr J < 0 and d_u, d_v ≥ 0, unstable modes grow at a real rate

Let $J$ be a real $2 \times 2$ matrix with $\operatorname{tr} J < 0$, let $d_u, d_v \ge 0$, let
$D = \operatorname{diag}(d_u, d_v)$, and let $k$ be real. If the Fourier mode of wavenumber $k$ is
[linearly unstable](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/is-unstable-mode.md),
that is, the mode matrix $J - k^2 D$ has a complex eigenvalue with positive real part, then its
[growth rate](growth-rate.md) $\lambda = (\tau + \sqrt{\tau^2 - 4\delta})/2$ ($\tau$, $\delta$ the
trace and determinant of $J - k^2 D$) is positive and is an eigenvalue of $J - k^2 D$ with a real
eigenvector: $\lambda > 0$ and $(J - k^2 D)\, v = \lambda v$ for some nonzero $v \in \mathbb{R}^2$.

The hypotheses include the Turing regime, where also $\det J > 0$. Under them an unstable mode has
$\delta < 0$
([criterion](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/is-unstable-mode-iff-dispersion-det-neg.md)),
so the eigenvalues of $J - k^2 D$ are real and of opposite signs: the unstable mode grows without
oscillating.
