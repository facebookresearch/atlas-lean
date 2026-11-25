# For tr J < 0 < det J, g_v ≤ 0: instability iff an admissible d_n < d

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the
Jacobian of the kinetics at a homogeneous steady state) with $\operatorname{tr} J < 0$, $\det J > 0$
and $g_v \le 0$, let $d_u \ge 0$, $d \ge 0$ and $L$ be real, and let $k_n = n\pi/L$ ($0$ for every
$n$ when $L = 0$) be the
[Neumann wavenumbers](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/neumann-wavenumber.md).
The homogeneous steady state is [linearly unstable on $[0, L]$](is-neumann-unstable.md) for the
diffusion matrix $\operatorname{diag}(d_u, d)$ if and only if some $n \in \mathbb{N}$ is admissible,
$f_u k_n^2 - d_u k_n^4 > 0$, with [neutral diffusion](neutral-diffusion.md) $d_n(k_n^2) < d$.

The criterion ranges over the discrete Neumann wavenumbers, not over all real wavenumbers. The onset
diffusion is the infimum of the admissible values $d_n(k_n^2)$, which need not be attained: for
$L \neq 0$, $d_u = 0$ and $f_u > 0$ every $n \ge 1$ is admissible and
$d_n(k_n^2) = \det J/(f_u k_n^2) \to 0$.
