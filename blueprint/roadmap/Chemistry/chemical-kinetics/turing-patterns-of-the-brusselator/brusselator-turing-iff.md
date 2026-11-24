# For a > 0 and b < 1 + a², the Turing threshold of the Brusselator

Let $a > 0$, $b < 1 + a^2$ and $d > 0$, and take the diffusion coefficients $d_u = 1$ of the
activator and $d_v = d$ of the inhibitor. Let $J$ be the
[Brusselator Jacobian](brusselator-jacobian.md). Then some Fourier mode is
[linearly unstable](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/is-unstable-mode.md),
that is, for some real wavenumber $k$ the
[mode matrix](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/mode-matrix.md)
$J - k^2 \operatorname{diag}(1, d)$ has a complex eigenvalue with positive real part, if and only if

$$2 a \sqrt{d} < d (b - 1) - a^2,$$

equivalently $b > (1 + a / \sqrt{d})^2$. The condition $b < 1 + a^2$ makes the steady state stable
without diffusion, since then $\operatorname{tr} J = b - 1 - a^2 < 0$ and $\det J = a^2 > 0$; it is
the case of the
[Turing criterion](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/exists-is-unstable-mode-iff.md)
for this Jacobian.
