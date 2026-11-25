# For tr J < 0, a band between consecutive k_n² leaves no unstable mode

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the
Jacobian of the kinetics at a homogeneous steady state) with $\operatorname{tr} J < 0$, let
$d_u, d_v > 0$, let $L > 0$ and $n \in \mathbb{N}$, and let $q_\pm$ be the
[lower](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/band-lower.md)
and
[upper](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/band-upper.md)
ends of the unstable band of squared wavenumbers,
$q_\pm = (d_v f_u + d_u g_v \pm \sqrt{\Delta})/(2 d_u d_v)$ with
$\Delta = (d_v f_u + d_u g_v)^2 - 4 d_u d_v \det J$ and $\sqrt{\Delta}$ read as $0$ for
$\Delta < 0$, in which case $q_- = q_+$ and the band is empty. If

$$(n\pi/L)^2 \le q_- \quad \text{and} \quad q_+ \le ((n + 1)\pi/L)^2,$$

then the homogeneous steady state is not [linearly unstable on $[0, L]$](is-neumann-unstable.md).
When the band is nonempty ($q_- < q_+$) every real wavenumber $k$ with $k^2 \in (q_-, q_+)$ is
unstable, so the problem on the whole line is unstable while the interval is not.
