# Linear instability on an interval with Neumann boundary conditions

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the
Jacobian of the kinetics at a homogeneous steady state), let $d_u, d_v$ be real and
$D = \operatorname{diag}(d_u, d_v)$, and let $L$ be real. The homogeneous steady state is linearly
unstable on $[0, L]$ when some [Neumann eigenvalue](is-neumann-eigenvalue.md), an eigenvalue of a
mode matrix $J - k_n^2 D$ at one of the
[Neumann wavenumbers](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/neumann-wavenumber.md)
$k_n = n\pi/L$ ($n \in \mathbb{N}$, all $0$ when $L = 0$), has positive real part. This is
meaningful for $L > 0$; at $L = 0$ it holds exactly when $J$ itself has an eigenvalue with positive
real part, although there is then no domain.

In the model $d_u, d_v > 0$; the definition is stated for all real values.
