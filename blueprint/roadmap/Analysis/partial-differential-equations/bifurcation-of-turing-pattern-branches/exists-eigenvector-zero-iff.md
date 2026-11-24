# Zero is an eigenvalue of the mode matrix iff the mode is neutral

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the
Jacobian of the kinetics at a homogeneous steady state), and let $d_u$, $d$ and $k$ be real. Then
$0$ is an eigenvalue of the
[mode matrix](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/mode-matrix.md)
$J - k^2 \operatorname{diag}(d_u, d)$ (with a nonzero complex eigenvector) if and only if
$h_d(k^2) = 0$, where $h_d(q) = d_u d q^2 - (d f_u + d_u g_v) q + \det J$ is the
[dispersion polynomial](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/dispersion-det.md).

In the model $d_u, d > 0$; the statement holds for all real values.
