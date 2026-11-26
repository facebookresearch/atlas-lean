# On mode fields, D u″ + J u is the mode operator on the coefficients

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the
Jacobian of the kinetics at a homogeneous steady state), let $\iota$ be a finite set of modes with
real wavenumbers $\kappa_i$, let $d_u, d$ be real, and write $M_i = J - \kappa_i^2 D$ for the
[mode matrices](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/mode-matrix.md),
$D = \operatorname{diag}(d_u, d)$. For every coefficient field $w$ and every real $x$, the
[mode field](mode-field.md) $u(x) = \sum_i \cos(\kappa_i x)\, w_i$ satisfies

$$D\, u''(x) + J\, u(x) = \sum_{i \in \iota} \cos(\kappa_i x)\, (J - \kappa_i^2 D)\, w_i,$$

the mode field of the [mode operator](mode-operator.md) applied to $w$.
