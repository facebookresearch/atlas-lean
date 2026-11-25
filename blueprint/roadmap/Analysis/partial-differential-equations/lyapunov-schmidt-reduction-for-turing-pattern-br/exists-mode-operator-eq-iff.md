# For f_v ≠ 0 and a simple critical mode i₀, the range is ker ψ

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the
Jacobian of the kinetics at a homogeneous steady state), let $\iota$ be a finite set of modes with
real wavenumbers $\kappa_i$, let $d_u, d$ be real, and write $M_i = J - \kappa_i^2 D$ for the
[mode matrices](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/mode-matrix.md),
$D = \operatorname{diag}(d_u, d)$. Assume the mode $i_0$ is critical, $\det M_{i_0} = 0$, that
$f_v \neq 0$, and that no other mode is critical: $\det M_i \neq 0$ for $i \neq i_0$ (critical and
non-resonant: a simple critical mode). Then a coefficient field $y$ is in the range of the
[mode operator](mode-operator.md) if and only if $\psi(y) = 0$, where
$\psi(y) = (M_{i_0})_{11}\, y_{i_0, 0} - f_v\, y_{i_0, 1}$ is the
[critical functional](critical-functional.md): the range has codimension one.
