# Critical functional from the row (m₁₁, −f_v) of mode i₀

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the
Jacobian of the kinetics at a homogeneous steady state), let $\iota$ be a finite set of modes with
real wavenumbers $\kappa_i$, let $d_u, d$ be real, and write $M_i = J - \kappa_i^2 D$ for the
[mode matrices](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/mode-matrix.md),
$D = \operatorname{diag}(d_u, d)$, and let $i_0 \in \iota$. The critical functional is the linear
functional on coefficient fields $y = (y_i)_{i \in \iota}$, $y_i \in \mathbb{R}^2$,

$$\psi(y) = (M_{i_0})_{11}\, y_{i_0, 0} - f_v\, y_{i_0, 1},$$

with $(M_{i_0})_{11} = g_v - \kappa_{i_0}^2 d$. Since $(m_{11}, -m_{01})\, M = (\det M, 0)$ and
$m_{01} = f_v$, the row $((M_{i_0})_{11}, -f_v)$ is a left null vector of $M_{i_0}$ when
$\det M_{i_0} = 0$: the functional then vanishes on the range of the
[mode operator](mode-operator.md).
