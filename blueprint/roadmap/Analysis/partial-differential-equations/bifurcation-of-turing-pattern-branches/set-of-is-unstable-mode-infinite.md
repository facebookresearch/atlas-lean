# Under the band condition, infinitely many wavenumbers are unstable

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the
Jacobian of the kinetics at a homogeneous steady state), let $d_u, d_v > 0$ and
$D = \operatorname{diag}(d_u, d_v)$, and assume $\operatorname{tr} J < 0$ and

$$2 \sqrt{d_u d_v \det J} < d_v f_u + d_u g_v,$$

with $\sqrt{x}$ read as $0$ for $x < 0$. Then infinitely many real wavenumbers $k$ are
[linearly unstable](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/is-unstable-mode.md):
every $k$ with $k^2 \in (\max(q_-, 0), q_+)$ is, for the band ends $q_\pm$ of the
[dispersion polynomial](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/dispersion-det.md).
Because of the convention for $\sqrt{x}$, these hypotheses do not imply $\det J > 0$: they are a
condition on the dispersion band, not stability of the kinetics without diffusion; adding
$\det J > 0$ gives Turing's criterion. By contrast, on an interval $[0, L]$ with $L > 0$ only
finitely many Neumann modes are unstable.
