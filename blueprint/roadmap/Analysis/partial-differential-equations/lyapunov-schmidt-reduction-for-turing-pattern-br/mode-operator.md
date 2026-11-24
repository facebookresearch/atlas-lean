# Linearized Turing operator on coefficients of finitely many modes

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the
Jacobian of the kinetics at a homogeneous steady state), let $\iota$ be a finite set of modes with
real wavenumbers $\kappa_i$, let $d_u, d$ be real, and write $M_i = J - \kappa_i^2 D$ for the
[mode matrices](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/mode-matrix.md),
$D = \operatorname{diag}(d_u, d)$. The mode operator is the linear map on coefficient fields
$w = (w_i)_{i \in \iota}$, $w_i \in \mathbb{R}^2$, that acts block-diagonally:

$$w \mapsto \bigl((J - \kappa_i^2 D)\, w_i\bigr)_{i \in \iota}.$$

On the field $u(x) = \sum_i \cos(\kappa_i x)\, w_i$ it is the linearization
$u \mapsto D u_{xx} + J u$ ([identity on mode fields](diffusion-mul-vec-deriv-deriv-add.md)). With
the Neumann wavenumbers $\kappa_n = n\pi/\ell$, $n < N$, it is a Galerkin truncation of the
linearized Turing operator on $[0, \ell]$ with Neumann boundary conditions.
