# At d_n(k²), with f_u k² ≠ d_u k⁴, the eigenvalues are 0 and the trace

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the
Jacobian of the kinetics at a homogeneous steady state), let $d_u$ and $k$ be real with
$f_u k^2 - d_u k^4 \neq 0$, and let $d = d_n(k^2)$ be the [neutral diffusion](neutral-diffusion.md).
Then a complex number $\mu$ is an eigenvalue of the
[mode matrix](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/mode-matrix.md)
$J - k^2 \operatorname{diag}(d_u, d)$ if and only if $\mu = 0$ or
$\mu = \operatorname{tr} J - k^2 (d_u + d)$, the trace of that matrix.

In the model $d_u > 0$; the statement holds for all real values with $f_u k^2 - d_u k^4 \neq 0$.
