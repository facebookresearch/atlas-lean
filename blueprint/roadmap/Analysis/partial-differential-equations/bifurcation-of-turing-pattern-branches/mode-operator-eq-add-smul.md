# The Turing linearization is affine in the inhibitor diffusion

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the
Jacobian of the kinetics at a homogeneous steady state), let $\iota$ be a finite set of modes with
real wavenumbers $\kappa_i$, and let $d_u$, $d$ and $d_0$ be real. On coefficient fields
$w = (w_i)_{i \in \iota}$, the
[mode operator](../lyapunov-schmidt-reduction-for-turing-pattern-br/mode-operator.md)
$w \mapsto ((J - \kappa_i^2 \operatorname{diag}(d_u, d))\, w_i)_i$ satisfies

$$\text{(mode operator at } d) = \text{(mode operator at } d_0) + (d - d_0)\, L_1,$$

where $L_1$ is the mode operator of the zero matrix with diffusion $\operatorname{diag}(0, 1)$,
$L_1 w = (-\kappa_i^2 \operatorname{diag}(0, 1)\, w_i)_i$: the mode form of
$\operatorname{diag}(0, 1)\, \partial_{xx}$.
