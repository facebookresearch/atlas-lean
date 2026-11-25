# For f_u q − d_u q² ≠ 0, h(q) = (f_u q − d_u q²)(d_n(q) − d)

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the
Jacobian of the kinetics at a homogeneous steady state), and let $d_u$, $d$ and $q$ be real with
$f_u q - d_u q^2 \neq 0$. With inhibitor diffusion $d$, the
[dispersion polynomial](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/dispersion-det.md)
$h_d(q) = d_u d q^2 - (d f_u + d_u g_v) q + \det J$ factors through the
[neutral diffusion](neutral-diffusion.md) $d_n(q) = (\det J - d_u g_v q)/(f_u q - d_u q^2)$:

$$h_d(q) = (f_u q - d_u q^2)\,\bigl(d_n(q) - d\bigr).$$

In the model $d_u, d > 0$ and $q > 0$; the identity holds for all real values with
$f_u q - d_u q^2 \neq 0$.
