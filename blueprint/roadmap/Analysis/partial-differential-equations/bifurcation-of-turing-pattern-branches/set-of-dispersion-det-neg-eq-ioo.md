# For d_u, d_v > 0 and positive discriminant, h < 0 exactly on (q₋, q₊)

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the
Jacobian of the kinetics at a homogeneous steady state), and let $d_u, d_v > 0$. Consider the
[dispersion polynomial](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/dispersion-det.md)
$h(q) = d_u d_v q^2 - (d_v f_u + d_u g_v) q + \det J$. If the
[band discriminant](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/band-discriminant.md)
$\Delta = (d_v f_u + d_u g_v)^2 - 4 d_u d_v \det J$ is positive, then the set of real $q$ with
$h(q) < 0$ is the open interval $(q_-, q_+)$ between the
[lower](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/band-lower.md)
and
[upper](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/band-upper.md)
band ends $q_\pm = (d_v f_u + d_u g_v \pm \sqrt{\Delta})/(2 d_u d_v)$.
