# The critical functional on the critical mode is f_v tr(J − κ²D)

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the
Jacobian of the kinetics at a homogeneous steady state), let $\iota$ be a finite set of modes with
real wavenumbers $\kappa_i$, let $d_u, d$ be real, write $D(d) = \operatorname{diag}(d_u, d)$, and
let $i_0 \in \iota$. Let $\varphi$ be the
[critical mode](../lyapunov-schmidt-reduction-for-turing-pattern-br/critical-mode.md) of $i_0$, the
coefficient field equal to $(f_v,\ \kappa_{i_0}^2 d_u - f_u)$ in mode $i_0$ and $0$ elsewhere, and
$\psi$ the
[critical functional](../lyapunov-schmidt-reduction-for-turing-pattern-br/critical-functional.md)
$\psi(y) = (g_v - \kappa_{i_0}^2 d)\, y_{i_0, 0} - f_v\, y_{i_0, 1}$. Then

$$\psi(\varphi) = f_v\,\bigl(\operatorname{tr} J - \kappa_{i_0}^2 (d_u + d)\bigr),$$

that is, $f_v$ times the trace of the mode matrix $J - \kappa_{i_0}^2 D(d)$.
