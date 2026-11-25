# Critical mode: the kernel vector of the mode matrix in mode i₀

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the
Jacobian of the kinetics at a homogeneous steady state), let $\iota$ be a finite set of modes with
real wavenumbers $\kappa_i$, let $d_u, d$ be real, and write $M_i = J - \kappa_i^2 D$ for the
[mode matrices](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/mode-matrix.md),
$D = \operatorname{diag}(d_u, d)$, and let $i_0 \in \iota$. The critical mode is the coefficient
field equal to the [kernel vector](ker-vec.md)
$((M_{i_0})_{01}, -(M_{i_0})_{00}) = (f_v,\ \kappa_{i_0}^2 d_u - f_u)$ in mode $i_0$ and to $0$ in
every other mode. When $\det M_{i_0} = 0$ it lies in the kernel of the
[mode operator](mode-operator.md).
