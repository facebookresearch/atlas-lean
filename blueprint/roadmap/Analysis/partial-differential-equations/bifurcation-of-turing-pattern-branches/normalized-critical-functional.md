# Critical functional normalized by its value on the critical mode

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the
Jacobian of the kinetics at a homogeneous steady state), let $\iota$ be a finite set of modes with
real wavenumbers $\kappa_i$, let $d_u, d$ be real, write $D(d) = \operatorname{diag}(d_u, d)$, and
let $i_0 \in \iota$. Let $\varphi$ be the
[critical mode](../lyapunov-schmidt-reduction-for-turing-pattern-br/critical-mode.md) of $i_0$, the
coefficient field equal to $(f_v,\ \kappa_{i_0}^2 d_u - f_u)$ in mode $i_0$ and $0$ elsewhere, and
$\psi$ the
[critical functional](../lyapunov-schmidt-reduction-for-turing-pattern-br/critical-functional.md)
$\psi(y) = (g_v - \kappa_{i_0}^2 d)\, y_{i_0, 0} - f_v\, y_{i_0, 1}$. The normalized critical
functional is

$$\hat\psi = \psi(\varphi)^{-1}\, \psi,$$

with $0^{-1}$ read as $0$. Since
$\psi(\varphi) = f_v\,(\operatorname{tr} J - \kappa_{i_0}^2 (d_u + d))$
([value on the critical mode](critical-functional-critical-mode.md)), when this is nonzero
$\hat\psi(\varphi) = 1$ and $\hat\psi$ has the same kernel as $\psi$, which is the
[range of the linearization](../lyapunov-schmidt-reduction-for-turing-pattern-br/exists-mode-operator-eq-iff.md)
when $i_0$ is critical and no other mode is ($\det(J - \kappa_i^2 D(d)) \neq 0$ for $i \neq i_0$).
When $\psi(\varphi) = 0$ the normalized functional is $0$.
