# At a neutral mode with negative trace, λ₊ has an explicit d-derivative

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the
Jacobian of the kinetics at a homogeneous steady state), let $d_u$, $d_0$ and $k$ be real, and let
$D(d) = \operatorname{diag}(d_u, d)$. Assume the mode $k$ is neutral at $d_0$, $h_{d_0}(k^2) = 0$
for the
[dispersion polynomial](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/dispersion-det.md)
$h_d(q) = d_u d q^2 - (d f_u + d_u g_v) q + \det J$, and that its trace is negative there,
$\operatorname{tr} J - k^2 (d_u + d_0) < 0$. Then the map $d \mapsto \lambda_+(J - k^2 D(d))$, with
$\lambda_+$ the [leading real eigenvalue](leading-eigenvalue.md), is differentiable at $d_0$ with
derivative

$$\frac{d_u k^4 - f_u k^2}{\operatorname{tr} J - k^2 (d_u + d_0)}.$$

In the model $d_u, d_0 > 0$; the statement holds for all real values.
