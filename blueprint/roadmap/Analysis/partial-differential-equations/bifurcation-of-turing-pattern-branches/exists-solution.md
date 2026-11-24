# A Neumann eigenvalue gives a zero-flux solution e^(μt) cos(k_n x) v

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the
Jacobian of the kinetics at a homogeneous steady state), let $d_u, d_v$ be real and
$D = \operatorname{diag}(d_u, d_v)$, and let $L \neq 0$. If $\mu$ is a
[Neumann eigenvalue](is-neumann-eigenvalue.md), then there are $n \in \mathbb{N}$ and a nonzero
$v \in \mathbb{C}^2$ such that the
[Fourier mode](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/fourier-mode.md)
$w(t, x) = e^{\mu t} \cos(k_n x)\, v$, with $k_n = n\pi/L$, is a
[classical solution](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/is-linearized-solution.md)
of the linearized system $w_t = D w_{xx} + J w$ on $\mathbb{R} \times \mathbb{R}$, and for every $t$
its $x$-derivative vanishes at $x = 0$ and at $x = L$ (zero flux at both ends).

In the model $d_u, d_v > 0$ and $L > 0$; the statement holds for all real $d_u, d_v$ and $L \neq 0$.
