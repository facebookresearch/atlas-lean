# Classical solution of the linearized reaction-diffusion system

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the Jacobian of the kinetics at a steady state) and let $d_u, d_v$ be real diffusion coefficients, and let $D = \operatorname{diag}(d_u, d_v)$. A function
$w \colon \mathbb{R} \times \mathbb{R} \to \mathbb{C}^2$, $(t, x) \mapsto w(t, x)$, is a classical
solution of the linearized reaction–diffusion system $w_t = D w_{xx} + J w$ when there are functions
$w_x, w_{xx} \colon \mathbb{R} \times \mathbb{R} \to \mathbb{C}^2$ such that for all $t$ and $x$:
$x \mapsto w(t, x)$ has derivative $w_x(t, x)$ at $x$, $x \mapsto w_x(t, x)$ has derivative
$w_{xx}(t, x)$ at $x$, and $s \mapsto w(s, x)$ has derivative $D\, w_{xx}(t, x) + J\, w(t, x)$ at
$s = t$.
