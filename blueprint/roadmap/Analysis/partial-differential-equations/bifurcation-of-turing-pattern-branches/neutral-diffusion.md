# Neutral diffusion d_n(q) of a squared wavenumber

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the
Jacobian of the kinetics at a homogeneous steady state), and let $d_u$ and $q$ be real. The neutral
diffusion of the squared wavenumber $q$ is

$$d_n(q) = \frac{\det J - d_u g_v q}{f_u q - d_u q^2},$$

read as $0$ when $f_u q - d_u q^2 = 0$. Since the
[dispersion polynomial](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/dispersion-det.md)
is affine in the inhibitor diffusion $d_v$, for $f_u q - d_u q^2 \neq 0$ the mode of squared
wavenumber $q$ is neutral ($\det(J - q \operatorname{diag}(d_u, d_v)) = 0$) exactly when
$d_v = d_n(q)$. For a Neumann mode, $q = k_n^2$, this is the diffusion at which an eigenvalue of its
mode matrix crosses zero.

In the model $d_u > 0$ and $q > 0$; the definition is stated for all real values.
