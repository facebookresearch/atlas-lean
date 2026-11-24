# The mode operator on finitely many modes is Fredholm

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the
Jacobian of the kinetics at a homogeneous steady state), let $\iota$ be a finite set of modes with
real wavenumbers $\kappa_i$, let $d_u, d$ be real, and write $M_i = J - \kappa_i^2 D$ for the
[mode matrices](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/mode-matrix.md),
$D = \operatorname{diag}(d_u, d)$. The [mode operator](mode-operator.md) $w \mapsto (M_i w_i)_i$ is
a Fredholm operator: its kernel is finite-dimensional and its range is closed of finite codimension.
This holds for every linear map between finite-dimensional spaces and uses no criticality
hypothesis; the kernel and range at a critical mode are computed separately.
