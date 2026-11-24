# Without resonance, only the neutral Neumann mode has eigenvalue 0

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the
Jacobian of the kinetics at a homogeneous steady state), let $d_u$, $d$ and $L$ be real, let
$k_m = m\pi/L$ be the
[Neumann wavenumbers](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/neumann-wavenumber.md),
and let $h_d(q) = d_u d q^2 - (d f_u + d_u g_v) q + \det J$ be the
[dispersion polynomial](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/dispersion-det.md).
If $h_d(k_n^2) = 0$ for the mode $n$ and $h_d(k_m^2) \neq 0$ for every $m \neq n$, then $n$ is the
only Neumann mode whose mode matrix $J - k_m^2 \operatorname{diag}(d_u, d)$ has the eigenvalue $0$.

Simplicity of $0$ within mode $n$ also needs
$\operatorname{tr}(J - k_n^2 \operatorname{diag}(d_u, d)) \neq 0$
([eigenvalues at the neutral diffusion](exists-eigenvector-mode-matrix-iff-of-ne.md)); together
these give the spectral hypothesis of a simple-eigenvalue bifurcation on $[0, L]$.

In the model $d_u, d > 0$ and $L > 0$; the statement holds for all real values.
