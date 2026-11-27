# The critical functional on L₁φ is f_v (d_u κ⁴ − f_u κ²)

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the
Jacobian of the kinetics at a homogeneous steady state), let $\iota$ be a finite set of modes with
real wavenumbers $\kappa_i$, let $d_u, d$ be real, write $D(d) = \operatorname{diag}(d_u, d)$, and
let $i_0 \in \iota$. Let $\varphi$ be the
[critical mode](../lyapunov-schmidt-reduction-for-turing-pattern-br/critical-mode.md) of $i_0$, the
coefficient field equal to $(f_v,\ \kappa_{i_0}^2 d_u - f_u)$ in mode $i_0$ and $0$ elsewhere, and
$\psi$ the
[critical functional](../lyapunov-schmidt-reduction-for-turing-pattern-br/critical-functional.md)
$\psi(y) = (g_v - \kappa_{i_0}^2 d)\, y_{i_0, 0} - f_v\, y_{i_0, 1}$. Let
$L_1 w = (-\kappa_i^2 \operatorname{diag}(0, 1)\, w_i)_i$ be the derivative in $d$ of the
[mode operator](../lyapunov-schmidt-reduction-for-turing-pattern-br/mode-operator.md)
([affine dependence](mode-operator-eq-add-smul.md)). Then

$$\psi(L_1 \varphi) = f_v\,\bigl(d_u \kappa_{i_0}^4 - f_u \kappa_{i_0}^2\bigr).$$
