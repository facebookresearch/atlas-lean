# With negative trace, an admissible mode's eigenvalue crosses 0 at d_n

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the
Jacobian of the kinetics at a homogeneous steady state), let $d_u$ and $k$ be real with
$f_u k^2 - d_u k^4 > 0$ (an admissible mode), let $d_0 = d_n(k^2)$ be its
[neutral diffusion](neutral-diffusion.md), and assume $\operatorname{tr} J - k^2 (d_u + d_0) < 0$.
Write $D(d) = \operatorname{diag}(d_u, d)$ and let $\lambda_+$ be the
[leading real eigenvalue](leading-eigenvalue.md). Then

- $\lambda_+(J - k^2 D(d_0)) = 0$;
- $d \mapsto \lambda_+(J - k^2 D(d))$ is differentiable at $d_0$ with derivative
  $\sigma = (d_u k^4 - f_u k^2)/(\operatorname{tr} J - k^2 (d_u + d_0))$;
- $\sigma > 0$: the critical eigenvalue crosses zero with positive speed as $d$ increases through
  $d_0$.

In the model $d_u, d_0 > 0$; the statement holds for all real values.
